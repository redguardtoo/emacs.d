;; plastic.el  - Major mode for Plastic proof assistant
;;
;; Author: Paul Callaghan <P.C.Callaghan@durham.ac.uk>
;;
;; plastic.el,v 12.1 2012/08/30 14:30:23 monnier Exp

;; NOTES:
;;	remember to prefix all potential cmds with plastic-lit-string
;;	alternative is to fix the filtering


(require 'proof)

(eval-when-compile
  (require 'cl)
  (require 'span)
  (require 'proof-syntax)
  (require 'outline)
  (defvar plastic-keymap nil))

(require 'plastic-syntax)


;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; User Configuration ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;

;; I believe this is standard for Linux under RedHat -tms
(defcustom plastic-tags "TO BE DONE"
  "*The directory of the TAGS table for the Plastic library"
  :type 'file
  :group 'plastic)

(defcustom plastic-test-all-name "need_a_global_lib"
  "*The name of the LEGO module which inherits all other modules of the
  library."
  :type 'string
  :group 'plastic)

(eval-and-compile
(defvar plastic-lit-string
  ">"
  "*Prefix of literate lines. Set to empty string to get non-literate mode"))

(defcustom plastic-help-menu-list
  '(["The PLASTIC Reference Card" (browse-url plastic-www-refcard) t]
    ["The PLASTIC library (WWW)" (browse-url plastic-library-www-page)  t])
  "List of menu items, as defined in `easy-menu-define' for Plastic
  specific help."
  :type '(repeat sexp)
  :group 'plastic)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Configuration of Generic Proof Package ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Users should not need to change this.

(defvar plastic-shell-handle-output
  (lambda (cmd string) 
    (when (proof-string-match "^Module" cmd)
      ;; prevent output and just give a minibuffer message
      (setq proof-shell-last-output-kind 'systemspecific)
      (message "Imports done!")))
  "Acknowledge end of processing import declarations.")

(defconst plastic-process-config
  (concat plastic-lit-string
	  " &S ECHO No PrettyPrinting configuration implemented;\n")
  "Command to enable pretty printing of the Plastic process.
   Proof-General annotations triggered by a cmd-line opt
  ")

(defconst plastic-pretty-set-width "&S ECHO no PrettyWidth ;\n"
  "Command to adjust the linewidth for pretty printing of the Plastic
  process.")

(defconst plastic-interrupt-regexp "Interrupt.."
  "Regexp corresponding to an interrupt")


;; ----- web documentation

(defcustom plastic-www-home-page "http://www.dur.ac.uk/CARG/plastic.html"
  "Plastic home page URL."
  :type 'string
  :group 'plastic)

(defcustom plastic-www-latest-release
  (concat plastic-www-home-page "/current")
  "The WWW address for the latest Plastic release."
  :type 'string
  :group 'plastic)

(defcustom plastic-www-refcard
  plastic-www-home-page
  "URL for the Plastic reference card."
  :type 'string
  :group 'plastic)

(defcustom plastic-library-www-page
  (concat plastic-www-home-page "/library")
  "The HTML documentation of the Plastic library."
  :type 'string
  :group 'plastic)



;; ----- plastic-shell configuration options

(defcustom plastic-base
  "/usr/local/plastic"
  ;; da: was
  ;; "PLASTIC_BASE:TO_BE_CUSTOMISED"
  "*base dir of plastic distribution"
  :type 'string
  :group 'plastic)

(defvar plastic-prog-name
  (concat plastic-base "/bin/plastic")
  "*Name of program to run as plastic.")

(defun plastic-set-default-env-vars ()
  "defaults for the expected lib vars."
  (cond
    ((not (getenv "PLASTIC_LIB"))
		(setenv "PLASTIC_LIB" (concat plastic-base "/lib"))
		(setenv "PLASTIC_TEST" (concat plastic-base "/test"))
	)))

(defvar plastic-shell-cd
  (concat plastic-lit-string " &S ECHO no cd ;\n")
  "*Command of the inferior process to change the directory.")

(defvar plastic-shell-proof-completed-regexp "\\*\\*\\* QED \\*\\*\\*"
  "*Regular expression indicating that the proof has been completed.")

(defvar plastic-save-command-regexp
  (concat "^" (proof-ids-to-regexp plastic-keywords-save)))
(defvar plastic-goal-command-regexp
  (concat "^" (proof-ids-to-regexp plastic-keywords-goal)))

(defvar plastic-kill-goal-command
  (concat plastic-lit-string " &S ECHO KillRef not applicable;"))
(defvar plastic-forget-id-command
  (concat plastic-lit-string " &S Forget "))

(defvar plastic-undoable-commands-regexp
  (proof-ids-to-regexp '("Refine" "Intros" "intros" "Normal" "Claim" "Immed"))
  "Undoable list")

;; "Dnf" "Refine" "Intros" "intros" "Next" "Normal"
;;   "Qrepl" "Claim" "For" "Repeat" "Succeed" "Fail" "Try" "Assumption"
;;   "UTac" "Qnify" "qnify" "andE" "andI" "exE" "exI" "orIL" "orIR" "orE" "ImpI"
;;   "impE" "notI" "notE" "allI" "allE" "Expand" "Induction" "Immed"
;;   "Invert"

;; ----- outline

(defvar plastic-goal-regexp "\\?\\([0-9]+\\)")

(defvar plastic-outline-regexp
  (concat "[[*]\\|"
	  (proof-ids-to-regexp
	   '("Discharge" "DischargeKeep" "Freeze" "$?Goal" "Module" "Record" "Inductive"
     "Unfreeze"))))

(defvar plastic-outline-heading-end-regexp ";\\|\\*)")

(defvar plastic-shell-outline-regexp plastic-goal-regexp)
(defvar plastic-shell-outline-heading-end-regexp plastic-goal-regexp)

(defvar plastic-error-occurred
	nil
	"flag for whether undo is required for try or minibuffer cmds")


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;   Derived modes - they're here 'cos they define keymaps 'n stuff ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-derived-mode plastic-shell-mode proof-shell-mode
   "plastic-shell"
   ;; With nil argument for docstring, Emacs makes up a nice one.
   nil
   (plastic-shell-mode-config))

(define-derived-mode plastic-mode proof-mode
   "Plastic script"
     "Major mode for Plastic proof scripts.

\\{plastic-mode-map}"
   (plastic-mode-config)
   (easy-menu-change (list proof-general-name) (car proof-help-menu)
		     (append (cdr proof-help-menu) plastic-help-menu-list)))

(eval-and-compile
  (define-derived-mode plastic-response-mode proof-response-mode
    "PlasticResp" nil
    (setq font-lock-keywords plastic-font-lock-terms)
    (plastic-init-syntax-table)
    (proof-response-config-done)))

(define-derived-mode plastic-goals-mode proof-goals-mode
  "PlasticGoals" "Plastic Goal State"
  (plastic-goals-mode-config))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;   Code that's plastic specific                                      ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun plastic-count-undos (span)
  "This is how to work out what the undo commands are.
Given is the first SPAN which needs to be undone."
  (let ((ct 0) string i
	(tl (length proof-terminal-string)))
    (while span
      (setq string (span-property span 'cmd))
      (plastic-preprocessing)			;; dynamic scope, on string
      (cond ((eq (span-property span 'type) 'vanilla)
	     (if (or (proof-string-match plastic-undoable-commands-regexp string)
		     (and (proof-string-match "Equiv" string)
			  (not (proof-string-match "Equiv\\s +[TV]Reg" string))))
		 (setq ct (+ 1 ct))))
	    ((eq (span-property span 'type) 'pbp)
	     (setq i 0)
	     (while (< i (length string))
	       (if (string-equal (substring string i (+ i tl)) proof-terminal-string)
		   (incf ct))
	       (setq i (+ 1 i)))))
      (setq span (next-span span 'type)))
    (list (concat plastic-lit-string 
		  " &S Undo x" (int-to-string ct) proof-terminal-string))))

(defun plastic-goal-command-p (span)
  "Decide whether argument is a goal or not"			;; NEED CHG.
  (proof-string-match plastic-goal-command-regexp
		      (or (span-property span 'cmd) "")))

(defun plastic-find-and-forget (span)
	;; count the number of spans to undo.
	;; all spans are equal...
    ;; (NB the 'x' before the id is required so xNN looks like an id,
    ;;  so that Undo can be implemented via the tmp_cmd route.)
  (let (string (spans 0))
    (while span
      ;; FIXME da: should probably ignore comments/proverproc here?
      (setq string (span-property span 'cmd))
      (plastic-preprocessing)		;; dynamic scope, on string

      (cond
	 ((null string) nil)
	 ((or (string-match "^\\s-*import" string)
	      (string-match "^\\s-*test" string)
	      (string-match "^\\s-*\\$" string)
	      (string-match "^\\s-*#" string))
	  
	  ; da: put this instead of XEmacs code
	  (message "Can't Undo imports yet!  You must exit Plastic for this!")
	;    (popup-dialog-box
	;	(list (concat "Can't Undo imports yet\n"
	;			   "You have to exit Plastic for this\n")
	;	      ["ok, I'll do this" (lambda () t) t]))
	    (return)
	   )    ;; warn the user that undo of imports not yet working.
	 (t (incf spans))
      )
      (setq span (next-span span 'type))

    )
    (list (concat plastic-lit-string 
		  " &S Undo x" (int-to-string spans) 
		  proof-terminal-string))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;   Other stuff which is required to customise script management   ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun plastic-goal-hyp ()		;; not used.
  (cond
   ((looking-at plastic-goal-regexp)
    (cons 'goal (match-string 1)))
   ((looking-at proof-shell-assumption-regexp)
    (cons 'hyp (match-string 1)))
   (t nil)))


;; NEED TO REFINE THIS (may99)

(defun plastic-state-preserving-p (cmd)
  (not (proof-string-match plastic-undoable-commands-regexp cmd)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;   Commands specific to plastic                                      ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(eval-after-load "plastic" ;; da: so that plastic-lit-string can be changed
  '(progn
     (eval `(proof-defshortcut plastic-Intros
			       ,(concat plastic-lit-string "Intros ")  [(control i)]))
     (eval `(proof-defshortcut plastic-Refine
			       ,(concat plastic-lit-string "Refine ")  [(control r)]))
     (eval `(proof-defshortcut plastic-ReturnAll
			       ,(concat plastic-lit-string "ReturnAll ") [(control u)]))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;   Plastic shell startup and exit hooks                              ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defvar plastic-shell-current-line-width nil
  "Current line width of the Plastic process's pretty printing module.
  Its value will be updated whenever the corresponding screen gets
  selected.")

;; The line width needs to be adjusted if the PLASTIC process is
;; running and is out of sync with the screen width

(defun plastic-shell-adjust-line-width ()
  "Use Plastic's pretty printing facilities to adjust output line width.
   Checks the width in the `proof-goals-buffer'
   ACTUALLY - still need to work with this. (pcc, may99)"
   (and (proof-shell-live-buffer)
	(proof-with-current-buffer-if-exists proof-goals-buffer
	(let ((current-width
	       ;; Actually, one might sometimes
	       ;; want to get the width of the proof-response-buffer
	       ;; instead. Never mind.
	       (window-width (get-buffer-window proof-goals-buffer t))))

	   (if (equal current-width plastic-shell-current-line-width) ()
	     ; else
	     (setq plastic-shell-current-line-width current-width)
	     (set-buffer proof-shell-buffer)
	     (insert (format plastic-pretty-set-width (- current-width 1)))
	     )))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;   Configuring proof mode and setting up various utilities  ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun plastic-mode-config ()

  (setq proof-terminal-string ";")
  (setq proof-script-comment-start "(*")			;; these still active
  (setq proof-script-comment-end "*)")

  (setq proof-prog-name (concat plastic-prog-name ""))
  (setenv "PROOF_GENERAL" "") ;; signal to plastic, use annotations

  (setq proof-assistant-home-page plastic-www-home-page)

  (setq proof-showproof-command (concat plastic-lit-string " &S PrfCtxt")
	proof-goal-command      (concat plastic-lit-string " Claim %s;")
	proof-save-command      (concat plastic-lit-string " Save %s;") ;; analogue?
	proof-context-command   (concat plastic-lit-string " &S Ctxt 20"))

  (setq proof-showproof-command  (concat plastic-lit-string " &S PrfCtxt")
	proof-goal-command   (concat plastic-lit-string " Claim %s;")
	proof-save-command   (concat plastic-lit-string " Save %s;") ;; analogue?
	proof-context-command  (concat plastic-lit-string " &S Ctxt 20")
	   ;; show 20 things; see ^c+C...
	proof-info-command   (concat plastic-lit-string " &S Help"))

  (setq proof-goal-command-p 'plastic-goal-command-p
	proof-count-undos-fn 'plastic-count-undos
	proof-find-and-forget-fn 'plastic-find-and-forget
	pg-topterm-goalhyplit-fn 'plastic-goal-hyp
	proof-state-preserving-p 'plastic-state-preserving-p)

  (setq	proof-save-command-regexp plastic-save-command-regexp
	proof-goal-command-regexp plastic-goal-command-regexp
	proof-save-with-hole-regexp plastic-save-with-hole-regexp
	proof-goal-with-hole-regexp plastic-goal-with-hole-regexp
	proof-kill-goal-command plastic-kill-goal-command
	proof-indent-any-regexp
	(proof-regexp-alt
	 (proof-ids-to-regexp plastic-commands)
	 "\\s(" "\\s)"))

  (plastic-init-syntax-table)

  ;; da: I've moved these out of proof-config-done in proof-script.el
  (setq pbp-goal-command (concat "UNIMPLEMENTED"))
  (setq pbp-hyp-command (concat "UNIMPLEMENTED"))

;; font-lock

  (set proof-script-font-lock-keywords plastic-font-lock-keywords-1)

  (proof-config-done)

;; outline

  (make-local-variable 'outline-regexp)
  (setq outline-regexp plastic-outline-regexp)

  (make-local-variable 'outline-heading-end-regexp)
  (setq outline-heading-end-regexp plastic-outline-heading-end-regexp)

;; tags
  (cond ((boundp 'tags-table-list)
	 (make-local-variable 'tags-table-list)
	 (setq tags-table-list (cons plastic-tags tags-table-list))))

  (and (boundp 'tag-table-alist)
       (setq tag-table-alist
	     (append '(("\\.lf$"   . plastic-tags)
		       ("plastic"  . plastic-tags))
		     tag-table-alist)))

  (set (make-local-variable 'blink-matching-paren-dont-ignore-comments) t)

;; hooks and callbacks

  (add-hook 'proof-shell-insert-hook       'plastic-shell-adjust-line-width)
  (add-hook 'proof-shell-handle-error-or-interrupt-hook 'plastic-had-error)
  (add-hook 'proof-shell-insert-hook       'plastic-preprocessing)

;; (add-hook 'proof-shell-handle-error-or-interrupt-hook
;; (lambda()(goto-char (search-forward (regexp-quote proof-terminal-char)))))

;;  (add-hook 'proof-shell-handle-delayed-output-hook `plastic-show-shell-buffer t)
;; this forces display of shell-buffer after each cmd, rather than goals-buffer
;; it is not always necessary - could always add it as a toggle option?

;; set up the env.
  (plastic-set-default-env-vars)
  )

(defun plastic-show-shell-buffer ()
   "switch buffers."
   (display-buffer proof-shell-buffer)
   )


(defun plastic-equal-module-filename (module filename)
  "Returns `t' if MODULE is equal to the FILENAME and `nil' otherwise.
The directory and extension is stripped of FILENAME before the test."
  (equal module
	 (file-name-sans-extension (file-name-nondirectory filename))))

(defun plastic-shell-compute-new-files-list ()
  "Function to update `proof-included-files list'.
Value for `proof-shell-compute-new-files-list', which see.

For Plastic, we assume that module identifiers coincide with file names."
  (let ((module (match-string 1)))
    (cdr (member-if
	  (lambda (filename) (plastic-equal-module-filename module filename))
	  proof-included-files-list))))



(defun plastic-shell-mode-config ()
  (setq proof-shell-cd-cmd plastic-shell-cd
	proof-shell-proof-completed-regexp plastic-shell-proof-completed-regexp
	proof-shell-error-regexp plastic-error-regexp
	proof-shell-interrupt-regexp plastic-interrupt-regexp
	;; DEAD proof-shell-noise-regexp "Discharge\\.\\. "
	proof-shell-assumption-regexp plastic-id
	proof-shell-start-goals-regexp plastic-goal-regexp
	pg-subterm-first-special-char ?\360
	pg-subterm-start-char ?\372
	pg-subterm-sep-char ?\373
	pg-subterm-end-char ?\374
	pg-topterm-regexp "\375"
	proof-shell-eager-annotation-start "\376"
	;; FIXME da: if p-s-e-a-s is implemented, you should set
	;; proof-shell-eager-annotation-start-length=1 to
	;; avoid possibility of duplicating short messages.
	proof-shell-eager-annotation-end "\377"

	proof-shell-annotated-prompt-regexp "LF> \371"
	proof-shell-result-start "\372 Pbp result \373"
	proof-shell-result-end "\372 End Pbp result \373"
	proof-shell-start-goals-regexp "\372 Start of Goals \373"
	proof-shell-end-goals-regexp "\372 End of Goals \373"

	proof-shell-init-cmd plastic-process-config
	proof-shell-restart-cmd plastic-process-config
	pg-subterm-anns-use-stack nil
	proof-shell-handle-output-system-specific plastic-shell-handle-output
	plastic-shell-current-line-width nil

	proof-shell-process-file
	(cons "Creating mark \"\\(.*\\)\" \\[\\(.*\\)\\]"
	      (lambda () (let ((match (match-string 2)))
			      (if (equal match "") match
				(concat 
				 (file-name-sans-extension match) ".lf")))))

	proof-shell-retract-files-regexp "forgot back through Mark \"\\(.*\\)\""
	;; DEAD: proof-shell-font-lock-keywords plastic-font-lock-keywords-1

	proof-shell-compute-new-files-list 'plastic-shell-compute-new-files-list)

  (plastic-init-syntax-table)

  (proof-shell-config-done)
  )

(defun plastic-goals-mode-config ()
  (setq pg-goals-change-goal "Next %s;"
	pg-goals-error-regexp plastic-error-regexp)
  (setq proof-goals-font-lock-keywords plastic-font-lock-terms)
  (plastic-init-syntax-table)
  (proof-goals-config-done))



;;;;;;;;;;;;;;;;;
;; MY new additions.

(defun plastic-small-bar () (interactive) (insert "%------------------------------\n"))

(defun plastic-large-bar () (interactive) (insert "%-------------------------------------------------------------------------------\n"))

(defun plastic-preprocessing () ;; NB: dynamic scoping of string
   "clear comments and remove literate marks (ie, \\n> ) - acts on var string"

   (with-no-warnings
   ;; might want to use proof-string-match here if matching is going
   ;; to be case sensitive (see docs)

   (if (= 0 (length plastic-lit-string))
       string				; no-op if non-literate
					; remaining lines are the
					; Else. (what, no 'return'?)
   (setq string (concat "\n" string " "))   ;; seed routine below, & extra char
   (let* ;; da: let* not really needed, added to nuke byte-comp warnings.
       (x
	(i 0)
	(l (length string))
	(eat-rest (lambda ()
		    (aset string i ?\ )  ;; kill the \n or "-" at least
		    (incf i)
		    (while (and (< i l) (/= (aref string i) ?\n))
		      (aset string i ?\ )
		      (incf i) )))
	(keep-rest (lambda ()
		     (loop for x in (string-to-list plastic-lit-string)
		       do (aset string i ?\ ) (incf i))
		     (while (and (< i l)
				 (/= (aref string i) ?\n)
				 (/= (aref string i) ?-))
		       (incf i) ))))
     (while (< i l)
       (cond
	((eq 0 (string-match "--" (substring string i)))
	 (funcall eat-rest))		; comment.
	((eq 0 (string-match "\n\n" (substring string i)))
	 (aset string i ?\ )
	 (incf i))			; kill repeat \n
	((= (aref string i) ?\n)	; start of new line
	 (aset string i ?\ ) (incf i)	; remove \n
	 (if (eq 0 (string-match plastic-lit-string
				 (substring string i)))
	     (funcall keep-rest)	; code line.
	   (funcall eat-rest)		; non-code line
	   ))
	(t
	 (incf i))))			; else include.
     (setq string (replace-regexp-in-string "  +" " " string))
     (setq string (replace-regexp-in-string "^ +" "" string))
   (if (string-match "^\\s-*$" string)
       (setq string (concat "ECHO comment line" proof-terminal-string))
     string)))))


(defun plastic-all-ctxt ()
	"show the full ctxt"
	(interactive)
	(proof-shell-invisible-command
	      (concat plastic-lit-string " &S Ctxt" proof-terminal-string))
	)

(defun plastic-send-one-undo ()
	"send an Undo cmd"
    ;; FIXME etc
    ;; is like this because I don't want the undo output to be shown.
    (proof-shell-insert (concat plastic-lit-string " &S Undo;")
			'proof-done-invisible))

;; hacky expt version.
;; still don't understand the significance of cmd!

(defun plastic-minibuf-cmd (cmd)
    "do minibuffer cmd then undo it, if error-free."
    (interactive
     (list (read-string "Command: " nil 'proof-minibuffer-history)))
    (print "hello")
    (plastic-reset-error)
    (if (and proof-state-preserving-p
	   (not (funcall proof-state-preserving-p cmd)))
      (error "Command is not state preserving, I won't execute it!"))
    (proof-shell-invisible-command cmd)
    (plastic-call-if-no-error 'plastic-send-one-undo))

(defun plastic-minibuf ()
    "do minibuffer cmd then undo it, if error-free."
    (interactive)
    (plastic-reset-error)
    (plastic-send-minibuf)
    (plastic-call-if-no-error 'plastic-send-one-undo))

(defun plastic-synchro ()
    "do minibuffer cmd BUT DON'T UNDO IT - use if things go wrong!"
    (interactive)
    (plastic-send-minibuf))

(defun plastic-send-minibuf ()
    "take cmd from minibuffer - see doc for proof-minibuffer-cmd"
    (interactive)
    (let (cmd)
	(setq cmd (read-string "Command: " nil 'proof-minibuffer-history))
	(setq cmd (concat plastic-lit-string " " cmd proof-terminal-string))
	(proof-shell-invisible-command cmd)))

(defun plastic-had-error ()
    "sets var plastic-error-occurred, called from hook"
    (if (eq proof-shell-error-or-interrupt-seen 'error)
	(setq plastic-error-occurred t)))
(defun plastic-reset-error ()
    "UNsets var plastic-error-occurred, before minibuffer or try cmd"
    (setq plastic-error-occurred nil))
(defun plastic-call-if-no-error (fn)
    "wait for proof process to be idle, and call fn if error-free."
    (while proof-shell-busy (sleep-for 0.25))
    (if (not plastic-error-occurred) (funcall fn)))

(defun plastic-show-shell ()
    "shortcut to shell buffer"
    (interactive)
    (proof-switch-to-buffer proof-shell-buffer))

(define-key plastic-keymap [(control s)] 'plastic-small-bar)
(define-key plastic-keymap [(control l)] 'plastic-large-bar)
(define-key plastic-keymap [(control c)] 'plastic-all-ctxt)
(define-key plastic-keymap [(control v)] 'plastic-minibuf)
(define-key plastic-keymap [(control o)] 'plastic-synchro)
(define-key plastic-keymap [(control p)] 'plastic-show-shell)


;; original end.

;;;;;;;;;;;;;;;;;
;; hacky overriding of the toolbar command and C-c C-v action
;; my version handles literate characters.
;; (should do better for long-term though)

(defalias 'proof-toolbar-command 'plastic-minibuf)
(defalias 'proof-minibuffer-cmd  'plastic-minibuf)
	;; the latter doesn't seem to work (pcc, 05aug02)

;;;

(provide 'plastic)
