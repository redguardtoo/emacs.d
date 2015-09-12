;;; pg-autotest.el --- Simple testing framework for Proof General
;;
;; Copyright (C) 2005, 2009-11 LFCS Edinburgh, David Aspinall.
;; Authors:   David Aspinall
;;
;; License:   GPL (GNU GENERAL PUBLIC LICENSE)
;;
;;; Commentary:
;;
;; Support for running a series of scripted UI tests.
;;
;; TODO:
;; -- fix failure handling for scriptfile
;; -- add macros for defining test suites
;; -- add more precise functional tests to check results
;; -- add negative tests
;;
;; pg-autotest.el,v 12.0 2011/10/13 10:54:49 da Exp

(require 'proof-splash)
(setq proof-splash-enable nil)		; prevent splash when testing

(require 'proof)
(require 'proof-shell)
(require 'proof-utils)

;;; Code:

(defvar pg-autotest-success t
  "Flag indicating overall successful state of tests.")

(defvar pg-autotest-log t
  "Value for 'standard-output' during tests.")

;;; Some utilities

(defun pg-autotest-find-file (file)
  "Find FILE (relative to `proof-home-directory')."
  (let* ((name   (concat proof-home-directory file)))
    (if (file-exists-p name)
	(find-file name)
      (error (format "autotest: requested file %s does not exist" name)))))

(defun pg-autotest-find-file-restart (file)
  "Find FILE and make ready to script there."
  ;; Ensure scripting off; if completely full, will register, otherwise retract
  (proof-deactivate-scripting-auto)
  (pg-autotest-find-file file)
  (goto-char (point-min))
  (unless (proof-locked-region-empty-p)
    ;; Should retract and unregister if was completely full
    (proof-goto-point))
  (proof-shell-wait)
  (pg-autotest-test-assert-unprocessed file))

;;; Invoke a test

(defmacro pg-autotest-apply (fn &rest args)
  `(let ((scaffoldfn
	  (intern (concat "pg-autotest-"
			  (symbol-name (quote ,fn))))))
     (if (fboundp scaffoldfn)
	 (apply scaffoldfn (list ,@args))
       (pg-autotest-message
	"TEST:  %s"
	(prin1-to-string (cons (quote ,fn)
			       (quote ,args))))
       (apply (intern (concat "pg-autotest-test-"
			     (symbol-name (quote ,fn))))
	      (list ,@args)))))

(defmacro pg-autotest (fn &rest args)
  `(if debug-on-error
      (pg-autotest-apply ,fn ,@args)
     (unwind-protect
	 (progn
	   (setq standard-output pg-autotest-log)
	   (condition-case err
	       (pg-autotest-apply ,fn ,@args)
	     (error
	      (progn
		(setq pg-autotest-success nil)
		(pg-autotest-message
		 "ERROR %s: %s" (quote ,fn) (prin1-to-string err))))))
       (setq standard-output t))))

;;; Test output and timing

(defun pg-autotest-log (file)
  (save-excursion
    (find-file file)
    (setq buffer-save-without-query t)
    (erase-buffer)
    (setq pg-autotest-log (current-buffer))
    (pg-autotest-message (concat "Tests started "
				 (format-time-string "%D %H:%M")))))

(defun pg-autotest-message (msg &rest args)
  "Give message MSG in log file output and on display."
  (let ((fmsg   (if args (apply 'format msg args) msg)))
    (proof-with-current-buffer-if-exists
     pg-autotest-log
     (insert fmsg "\n"))
    (message "%s" fmsg)
    (redisplay t)))

(defun pg-autotest-remark (msg)
  (pg-autotest-message "\n\nREMARK: %s\n" msg))

(defun pg-autotest-timestart (&optional clockname)
  "Make a note of current time, named 'local or CLOCKNAME."
  (put 'pg-autotest-time (or clockname 'local)
       (current-time)))

(defun pg-autotest-timetaken (&optional clockname)
  "Report time since (startclock CLOCKNAME)."
  (let* ((timestart (get 'pg-autotest-time (or clockname 'local)))
	 (timetaken
	  (time-subtract (current-time) timestart)))
    (pg-autotest-message
     "TIME: %f (%s)"
     (float-time timetaken)
     (if clockname (symbol-name clockname)
       "this test"))))


;;; Start up and exit

(defun pg-autotest-start (&optional debug)
  "Start a session of tests.  DEBUG indicates to capture debug output."
  (when debug
    (setq debug-on-error t) 		; enable in case a test goes wrong
    (setq proof-general-debug t)	; debug messages from PG

    (defadvice proof-debug (before proof-debug-to-log (msg &rest args))
      "Output the debug message to the test log."
      (apply 'pg-autotest-message msg args))
    (ad-activate 'proof-debug)))

(defun pg-autotest-exit ()
  "Exit Emacs returning Unix success 0 if all tests succeeded."
  (pg-autotest-message (concat "\nTests completed "
			       (format-time-string "%D %H:%M")))
  (proof-with-current-buffer-if-exists
   pg-autotest-log
   (goto-char (point-max))
   (insert "\n\nContents of *Messages*:\n\n")
   (with-current-buffer (get-buffer "*Messages*")
     (append-to-buffer pg-autotest-log (point-min) (point-max)))
   (goto-char (point-max))
   (when (get-buffer "*PG Debug*")
     (insert "\n\nContents of *PG Debug*:\n\n")
     (proof-with-current-buffer-if-exists (get-buffer "*PG Debug*"))
     (append-to-buffer pg-autotest-log (point-min) (point-max)))
   (save-buffer 0))
  (kill-emacs (if pg-autotest-success 0 1)))

;;; The test script functions proper
  
(defun pg-autotest-test-process-wholefile (file)
  "Load FILE and script in one go.
An error is signalled if scripting doesn't completely the whole buffer."
  (pg-autotest-find-file-restart file)
  (proof-process-buffer)
  (proof-shell-wait)
  (pg-autotest-test-assert-processed file))

(defun pg-autotest-test-script-wholefile (file)
  "Process FILE line-by-line, using `proof-shell-wait'.
An error is signalled if scripting doesn't complete."
  (pg-autotest-find-file-restart file)
  (save-excursion
    (let ((making-progress t) last-locked-end)
      (while making-progress
	(setq last-locked-end (proof-unprocessed-begin))
	(goto-char last-locked-end)
	(save-current-buffer
	  (condition-case err
	      (proof-assert-next-command-interactive)
	    (error
	     (let ((msg (car-safe (cdr-safe err))))
	       (unless (string-equal msg
                 ;; normal user error message at end of buffer
		  "At end of the locked region, nothing to do to!")
		 (pg-autotest-message
		  "proof-assert-next-command-interactive hit an error: %s"
		  msg)))))
	  (proof-shell-wait))
	(goto-char (proof-queue-or-locked-end))
	(setq making-progress (> (point) last-locked-end)))))
  (pg-autotest-test-assert-processed file))

(defun pg-autotest-test-script-randomjumps (file jumps)
  "Load FILE and process in it by jumping around randomly JUMPS times.
This should be robust against synchronization errors; we test this by
completely processing the buffer as the last step."
;; TODO: Additionally some edits are made but undone.
  (pg-autotest-find-file-restart file)
  (while (> jumps 0)
    (let* ((random-point     (random (point-max)))
	   (random-edit      nil) ; (< 20 (random 100)))
	   (random-thing     (random 10)))
      (cond
       ((and (eq random-thing 0)
	     (not (proof-locked-region-full-p)))
	(pg-autotest-message
	 " random jump: processing whole buffer")
	(proof-process-buffer)
	(proof-shell-wait)
	(decf jumps))

	((and (eq random-thing 1) 
	      (not (proof-locked-region-empty-p)))
	 (pg-autotest-message
	  " random jump: retracting whole buffer")
	 (proof-retract-buffer)
	 (proof-shell-wait)
	 (decf jumps))

	(t
	 (pg-autotest-message
	  " random jump: going to point: %d" random-point))
	 (goto-char random-point)
	 (unless (if (>= (point) (proof-unprocessed-begin))
		     (proof-only-whitespace-to-locked-region-p))
	   (proof-goto-point)
	   (if (eq random-thing 2)
	       (progn ;; interrupt after 2 secs
		 (sit-for 1)
		 (sit-for 1)
		 (when proof-shell-busy
		   (pg-autotest-message
		    " random jump: interrupting prover")
		   (proof-interrupt-process)))
	     (proof-shell-wait))
	   (decf jumps)))))
  (unless (proof-locked-region-full-p)
    (proof-process-buffer)
    (proof-shell-wait))
  (pg-autotest-test-assert-processed file))

(defun pg-autotest-test-retract-file (file)
  (save-excursion
    (pg-autotest-find-file file)
    (proof-retract-buffer)
    (sit-for 1)))

(defun pg-autotest-test-assert-processed (file)
  "Check that FILE has been fully processed."
  (save-excursion ;; TODO: also check on included files list
    (pg-autotest-find-file file)
    (pg-autotest-test-assert-full)))

(defun pg-autotest-test-assert-full ()
  "Check that current buffer has been fully processed."
  (proof-shell-wait)
  (unless (proof-locked-region-full-p)
    (error (format "Locked region in buffer `%s' is not full"
		   (buffer-name)))))

(defun pg-autotest-test-assert-unprocessed (file)
  "Check that FILE has been fully unprocessed."
  (save-excursion
    (pg-autotest-find-file file)
    (unless (proof-locked-region-empty-p)
      (error (format "Locked region in file `%s' is not empty" file)))))

(defun pg-autotest-test-eval (body)
  "Evaluate given expression for side effect."
  (eval body))

(defun pg-autotest-test-quit-prover ()
  "Exit prover process."
  (if (buffer-live-p proof-shell-buffer)
      (let ((kill-buffer-query-functions nil)) 
	(kill-buffer proof-shell-buffer))
    (error "No proof shell buffer to kill")))





(provide 'pg-autotest)
;;; pg-autotest.el ends here
