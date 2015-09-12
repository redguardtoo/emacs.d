;; pg-response.el --- Proof General response buffer mode.
;;
;; Copyright (C) 1994-2010 LFCS Edinburgh.
;; Authors:   David Aspinall, Healfdene Goguen,
;;		Thomas Kleymann and Dilip Sequeira
;; License:   GPL (GNU GENERAL PUBLIC LICENSE)
;;
;; pg-response.el,v 12.10 2012/09/25 09:44:18 pier Exp
;;
;;; Commentary:
;;
;; This mode is used for the response buffer proper, and
;; also the trace and theorems buffer.  A sub-module of proof-shell.
;;

;;; Code:

(eval-when-compile
  (require 'easymenu)	  ; easy-menu-add
  (require 'proof-utils)  ; deflocal, proof-eval-when-ready-for-assistant
  (defvar proof-response-mode-menu nil)
  (defvar proof-assistant-menu nil))

(require 'pg-assoc)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Local variables
;;

(deflocal pg-response-eagerly-raise t
  "Non-nil if this buffer will be eagerly raised/displayed on startup.")


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Response buffer mode
;;

;;;###autoload
(define-derived-mode proof-response-mode proof-universal-keys-only-mode
  "PGResp" "Responses from Proof Assistant"
  (setq proof-buffer-type 'response)
  (add-hook 'kill-buffer-hook 'pg-save-from-death nil t)
  (easy-menu-add proof-response-mode-menu proof-response-mode-map)
  (easy-menu-add proof-assistant-menu proof-response-mode-map)
  (proof-toolbar-setup)
  (setq pg-response-next-error nil)
  (buffer-disable-undo)
  (if proof-keep-response-history (bufhist-mode)) ; history for contents
  (set-buffer-modified-p nil)
  (setq buffer-read-only t)
  (setq cursor-in-non-selected-windows nil))

;;
;; Menu for response buffer
;;
(proof-eval-when-ready-for-assistant ; proof-aux-menu depends on <PA>
    (easy-menu-define proof-response-mode-menu
      proof-response-mode-map
      "Menu for Proof General response buffer."
      (proof-aux-menu)))

;;
;; Keys for response buffer
;;
;; TODO: use standard Emacs button behaviour here (cf Info mode)
(define-key proof-response-mode-map [mouse-1] 'pg-goals-button-action)
(define-key proof-response-mode-map [q] 'bury-buffer)
(define-key proof-response-mode-map [c] 'pg-response-clear-displays)


;;;###autoload
(defun proof-response-config-done ()
  "Complete initialisation of a response-mode derived buffer."
  (setq font-lock-defaults '(proof-response-font-lock-keywords)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Window configuration
;;   -- multiple frames for goals and response buffers,
;;   -- three window mode
;;

(defvar pg-response-special-display-regexp nil
  "Regexp for `special-display-regexps' for multiple frame use.
Internal variable, setting this will have no effect!")

(defconst proof-multiframe-parameters
  '((minibuffer . nil)
    (modeline . nil)			; ignored?
    (unsplittable . t)
    (menu-bar-lines . 0)
    (tool-bar-lines . nil)
    (proofgeneral . t)) ;; indicates generated for/by PG
  "List of GNU Emacs frame parameters for secondary frames.")

(defun proof-multiple-frames-enable ()
  (let ((spdres (cons
		 pg-response-special-display-regexp
		 proof-multiframe-parameters)))
    (if proof-multiple-frames-enable
	(add-to-list 'special-display-regexps spdres)
      (setq special-display-regexps
	    (delete spdres special-display-regexps))))
  (proof-layout-windows))

(defun proof-three-window-enable ()
  (proof-layout-windows))

(defun proof-select-three-b (b1 b2 b3 &optional policy)
  "Put the given three buffers into three windows.
Following POLICY, which can be one of 'smart, 'horizontal,
'vertical or 'hybrid."
  (interactive "bBuffer1:\nbBuffer2:\nbBuffer3:")
  (delete-other-windows)
  (switch-to-buffer b1)
  (let ((pol))
    (if (eq policy 'smart)
	(cond
	 ((>= (frame-width) (* 1.5 split-width-threshold))
	  (setq pol 'horizontal))
	 ((>= (frame-width) split-width-threshold)
	  (setq pol 'hybrid))
	 (t (setq pol 'vertical)))
      (setq pol policy))
    (message "policy = %S , pol = %S" policy pol)
  (save-selected-window
    (cond
     ((eq pol 'hybrid)
      (split-window-horizontally)
      (other-window 1)
      (switch-to-buffer b2)
      (proof-safe-split-window-vertically) ; enlarge vertically if necessary
      (other-window 1)
      (switch-to-buffer b3))
     ((eq pol 'vertical)
      (split-window-vertically)
      (other-window 1)
      (switch-to-buffer b2)
      (proof-safe-split-window-vertically) ; enlarge vertically if necessary
      (other-window 1)
      (switch-to-buffer b3))
     ((eq pol 'horizontal)
      (split-window-horizontally) ; horizontally again
      (other-window 1)
      (switch-to-buffer b2)
      (enlarge-window (/ (frame-width) 6) t) ; take 2/3 of width before splitting again
      (split-window-horizontally) ; horizontally again
      (other-window 1)
      (switch-to-buffer b3))))))




(defun proof-display-three-b (&optional policy)
  "Layout three buffers in a single frame.  Only do this if buffers exist."
  (interactive)
  (when (and (buffer-live-p proof-goals-buffer)
	     (buffer-live-p proof-response-buffer))
    (save-excursion
      (proof-select-three-b
       proof-script-buffer proof-goals-buffer proof-response-buffer
       policy))))

(defvar pg-frame-configuration nil
  "Variable storing last used frame configuration.")

;; FIXME: would be nice to try storing this persistently.
(defun pg-cache-frame-configuration ()
  "Cache the current frame configuration, between prover restarts."
  (setq pg-frame-configuration (current-frame-configuration)))

(defun proof-layout-windows ()
  "Refresh the display of windows according to current display mode.

For multiple frame mode, this function obeys the setting of
`pg-response-eagerly-raise', which see.

For single frame mode:

- In two panes mode, this uses a canonical layout made by splitting
Emacs windows in equal proportions. The splitting is vertical if
emacs width is smaller than `split-width-threshold' and
horizontal otherwise. You can then adjust the proportions by
dragging the separating bars.

- In three pane mode, there are three display modes, depending
  where the three useful buffers are displayed: scripting
  buffer, goals buffer and response buffer.

  Here are the three modes:

  - vertical: the 3 buffers are displayed in one column.
  - hybrid: 2 columns mode, left column displays scripting buffer
    and right column displays the 2 others.
  - horizontal: 3 columns mode, one for each buffer (script, goals,
    response).

  By default, the display mode is automatically chosen by
  considering the current emacs frame width: if it is smaller
  than `split-width-threshold' then vertical mode is chosen,
  otherwise if it is smaller than 1.5 * `split-width-threshold'
  then hybrid mode is chosen, finally if the frame is larger than
  1.5 * `split-width-threshold' then the horizontal mode is chosen.

  You can change the value of `split-width-threshold' at your
  will.

  If you want to force one of the layouts, you can set variable
  `proof-three-window-mode-policy' to 'vertical, 'horizontal or
  'hybrid. The default value is 'smart which sets the automatic
  behaviour described above."
  (interactive)
  (cond
   (proof-multiple-frames-enable
    (delete-other-windows) ;; hope we're on the right frame/window
    (if proof-script-buffer
	(switch-to-buffer proof-script-buffer))
    (proof-map-buffers (proof-associated-buffers)
      (if pg-response-eagerly-raise
	  (proof-display-and-keep-buffer (current-buffer) nil 'force)))
    ;; Restore an existing frame configuration (seems buggy, typical)
    (if pg-frame-configuration
	(set-frame-configuration pg-frame-configuration 'nodelete)))
   (proof-three-window-enable
    (proof-delete-other-frames)
    (set-window-dedicated-p (selected-window) nil)
    (proof-display-three-b proof-three-window-mode-policy))
   ;; Two-of-three window mode.
   ;; Show the response buffer as first in preference order.
   (t
    (proof-delete-other-frames)
    (set-window-dedicated-p (selected-window) nil)
    (delete-other-windows)
    (if (buffer-live-p proof-response-buffer)
	(proof-display-and-keep-buffer proof-response-buffer nil 'force))))
  (pg-hint (pg-response-buffers-hint)))

(defun proof-delete-other-frames ()
  "Delete frames showing associated buffers."
  (save-selected-window
    ;; FIXME: this is a bit too brutal.  If there is no
    ;; frame for the associated buffer, we may delete
    ;; the main frame!!
    (let ((mainframe
	   (window-frame
	    (if proof-script-buffer
		(proof-get-window-for-buffer proof-script-buffer)
	      ;; We may lose with just selected window
	      (selected-window)))))
      (proof-map-buffers (proof-associated-buffers)
	(let* ((win
		;; NB: g-w-f-b will re-display in new frame if
		;; the buffer isn't selected/visible.  This causes
		;; new frame to flash up and be deleted if already
		;; deleted!
		;; (proof-get-window-for-buffer (current-buffer))
		;; This next choice is probably better:
		(get-buffer-window (current-buffer) 'visible))
	       (fm (and win (window-frame win))))
	  (unless (equal mainframe fm)
	    (if fm (delete-frame fm))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Displaying in the response buffer
;;

;; Flag and function to keep response buffer tidy.
(defvar pg-response-erase-flag nil
  "Non-nil means the response buffer should be cleared before next message.")

;;;###autoload
(defun pg-response-maybe-erase
  (&optional erase-next-time clean-windows force keep)
  "Erase the response buffer, according to confusing flag combinations.

Mainly, we look at `pg-response-erase-flag' and clear the
response buffer if this is non-nil, but NOT the special
symbol 'invisible.

ERASE-NEXT-TIME is the new value for the flag.

FORCE overrides the flag to force cleaning.

KEEP overrides the flag to prevent cleaning.

FORCE takes precedent over KEEP.

If CLEAN-WINDOWS is set, use `proof-clean-buffer' to do the erasing,
otherwise we use `bufhist-checkpoint-and-erase' to record an
undo history entry for the current buffer contents.

If the user option `proof-tidy-response' is nil, the buffer
will never be cleared unless FORCE is set.

No effect if there is no response buffer currently.
Returns non-nil if response buffer was cleared."
  (when (buffer-live-p proof-response-buffer)
    (let ((inhibit-read-only t)
	  (doit (or (and
		     proof-tidy-response
		     (not keep)
		     (not (eq pg-response-erase-flag 'invisible))
		     pg-response-erase-flag)
		    force)))
      (if doit
	  (if clean-windows
	      (proof-clean-buffer proof-response-buffer)
	    (with-current-buffer proof-response-buffer
	      (setq pg-response-next-error nil)	; all error msgs lost!
	      (if (> (buffer-size) 0)
		  (bufhist-checkpoint-and-erase))
	      (set-buffer-modified-p nil))))
      (setq pg-response-erase-flag erase-next-time)
      doit)))

(defun pg-response-display (str)
  "Show STR as a response in the response buffer."

  (pg-response-maybe-erase t nil)
  (pg-response-display-with-face str)

  ;; NB: this displays an empty buffer sometimes when it's not
  ;; so useful.  It _is_ useful if the user has requested to
  ;; see the proof state and there is none
  ;; (Isabelle/Isar displays nothing: might be better if it did).
  (proof-display-and-keep-buffer proof-response-buffer))

;;
;; Images for the response buffer
;;
;(defimage pg-response-error-image
;  ((:type xpm :file "/home/da/PG/images/epg-interrupt.xpm")))

;(defimage pg-response-warning-image
;  ((:type xpm :file "/home/da/PG/images/epg-abort.xpm")))


;; TODO: this function should be combined with
;; pg-response-maybe-erase-buffer.
;;;###autoload
(defun pg-response-display-with-face (str &optional face)
  "Display STR with FACE in response buffer."
  (cond
   ((string-equal str ""))
   ((string-equal str "\n"))		; quick exit, no display.
   (t
    (let (start end)
      (with-current-buffer proof-response-buffer
	(setq buffer-read-only nil)
	;; da: I've moved newline before the string itself, to match
	;; the other cases when messages are inserted and to cope
	;; with warnings after delayed output (non newline terminated).
	(goto-char (point-max))
	;; insert a newline before the new message unless the
	;; buffer is empty
	(unless (eq (point-min) (point-max))
	  (newline))
	(setq start (point))
	(insert str)
	(unless (bolp) (newline))
	(when face
	  (overlay-put
	   (make-overlay start (point-max))
	   'face face))

	(setq buffer-read-only t)
	(set-buffer-modified-p nil))))))

(defun pg-response-clear-displays ()
  "Clear Proof General response and tracing buffers.
You can use this command to clear the output from these buffers when
it becomes overly long.  Particularly useful when `proof-tidy-response'
is set to nil, so responses are not cleared automatically."
  (interactive)
  (proof-with-current-buffer-if-exists proof-response-buffer
     (if (> (buffer-size) 0)
	 (let ((inhibit-read-only t))
	   (bufhist-checkpoint-and-erase)
	   (set-buffer-modified-p nil))))
  (proof-with-current-buffer-if-exists proof-trace-buffer
     (let ((inhibit-read-only t))
       (erase-buffer)
       (set-buffer-modified-p nil)))
  (message "Response buffers cleared."))

;;;###autoload
(defun pg-response-message (&rest args)
  "Issue the message ARGS in the response buffer and display it."
  (pg-response-display-with-face (apply 'concat args))
  (proof-display-and-keep-buffer proof-response-buffer))

;;;####autoload
(defun pg-response-warning (&rest args)
  "Issue the warning ARGS in the response buffer and display it.
The warning is coloured with `proof-warning-face'."
  (pg-response-display-with-face (apply 'concat args) 'proof-warning-face)
  (proof-display-and-keep-buffer proof-response-buffer))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Next error function.
;;

;;;###autoload
(defun proof-next-error (&optional argp)
  "Jump to location of next error reported in the response buffer.

A prefix arg specifies how many error messages to move;
negative means move back to previous error messages.

Optional argument ARGP means reparse the error message buffer
and start at the first error."
  (interactive "P")
  (if (and pg-next-error-regexp
       (or
	(buffer-live-p proof-response-buffer)
	(error "Next error: no response buffer to parse!")))
      (let ((wanted-error    (or (and (not (consp argp))
				      (+ (prefix-numeric-value argp)
					 (or pg-response-next-error 0)))
				 (and (consp argp) 1)
				 (or pg-response-next-error 1)))
	    line column file errpos)
	(set-buffer proof-response-buffer)
	(goto-char (point-min))
	(if (re-search-forward pg-next-error-regexp
			       nil t wanted-error)
	    (progn
	      (setq errpos (save-excursion
			     (goto-char (match-beginning 0))
			     (beginning-of-line)
			     (point)))
	      (setq line (match-string 2)) ; may be unset
	      (if line (setq line (string-to-number line)))
	      (setq column (match-string 3)) ; may be unset
	      (if column (setq column (string-to-number column)))
	      (setq pg-response-next-error wanted-error)
	      (if (and
		   pg-next-error-filename-regexp
		     ;; Look for the most recently mentioned filename
		     (re-search-backward
		      pg-next-error-filename-regexp nil t))
		    (setq file
			  (if (file-exists-p (match-string 2))
			      (match-string 2)
			    ;; May need post-processing to extract filename
			    (if pg-next-error-extract-filename
				(format
				 pg-next-error-extract-filename
				 (match-string 2))))))
		;; Now find the other buffer we need to display
		(let*
		    ((errbuf
		      (if file
			  (find-file-noselect file)
			(or proof-script-buffer
			    ;; Could make guesses, e.g. last active script
			    (error
			     "Next error: can't guess file for error message"))))
		     (pop-up-windows t)
		     (rebufwindow
		      (or (get-buffer-window proof-response-buffer 'visible)
			  ;; Pop up a window.
			  (display-buffer proof-response-buffer))))
		  ;; Make sure the response buffer stays where it is,
		  ;; and make sure source buffer is visible
		  (select-window rebufwindow)
		  (pop-to-buffer errbuf)
		  ;; Display the error message in the response buffer
		  (set-window-point rebufwindow errpos)
		  (set-window-start rebufwindow errpos)
		  ;; Find the error location in the error buffer
		  (set-buffer errbuf)
		  ;; FIXME: no handling of selective display here
		  (with-no-warnings ; "interactive only"
		   (goto-line line))
		  (if (and column (> column 1))
		      (move-to-column (1- column)))))
	    (setq pg-response-next-error nil)
	    (error "Next error: couldn't find a next error")))))

;;;###autoload
(defun pg-response-has-error-location ()
  "Return non-nil if the response buffer has an error location.
See `pg-next-error-regexp'."
  (if pg-next-error-regexp
      (proof-with-current-buffer-if-exists proof-response-buffer
	(save-excursion
	  (goto-char (point-min))
	  (re-search-forward pg-next-error-regexp nil t)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Tracing buffers
;;

(defcustom proof-trace-buffer-max-lines 10000
  "The maximum size in lines for Proof General *trace* buffers.
A value of 0 stands for unbounded."
  :type 'integer
  :group 'proof-shell)

;; An analogue of pg-response-display-with-face
(defun proof-trace-buffer-display (start end)
  "Copy region START END from current buffer to end of the trace buffer."
  (let ((cbuf   (current-buffer))
	(nbuf   proof-trace-buffer))
    (set-buffer nbuf)
    (save-excursion
      (goto-char (point-max))
      (let ((inhibit-read-only t))
	(insert ?\n)
	(insert-buffer-substring cbuf start end)
	(unless (bolp)
	  (insert ?\n))))
    (set-buffer cbuf)))

(defun proof-trace-buffer-finish ()
  "Call to complete a batch of tracing output.
The buffer is truncated if its size is greater than `proof-trace-buffer-max-lines'."
  (if (> proof-trace-buffer-max-lines 0)
      (proof-with-current-buffer-if-exists proof-trace-buffer
	(save-excursion
	  (goto-char (point-max))
	  (forward-line (- proof-trace-buffer-max-lines))
	  (let ((inhibit-read-only t))
	    (delete-region (point-min) (point)))))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Theorems buffer
;;
;; [ INCOMPLETE ]
;;
;; Revives an old idea from Isamode: a buffer displaying a bunch
;; of theorem names.
;;
;;

(defun pg-thms-buffer-clear ()
  "Clear the theorems buffer."
  (with-current-buffer proof-thms-buffer
    (let (start str)
      (goto-char (point-max))
      (newline)
      (setq start (point))
      (insert str)
      (unless (bolp) (newline))
      (set-buffer-modified-p nil))))


(provide 'pg-response)
;;; pg-response.el ends here
