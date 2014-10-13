;; lego.el Major mode for LEGO proof assistants
;; Copyright (C) 1994 - 1998 LFCS Edinburgh.
;; Author:      Thomas Kleymann and Dilip Sequeira
;; License:     GPL (GNU GENERAL PUBLIC LICENSE)
;; Maintainer: Paul Callaghan <P.C.Callaghan@durham.ac.uk>

;;
;; lego.el,v 12.1 2012/08/30 14:30:23 monnier Exp
;;

(require 'proof)
(require 'lego-syntax)
(eval-when-compile
  (require 'outline))

;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; User Configuration ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;

;; I believe this is standard for Linux under RedHat -tms
(defcustom lego-tags "/usr/lib/lego/lib_Type/"
  "*The directory of the TAGS table for the LEGO library"
  :type 'file
  :group 'lego)

(defcustom lego-test-all-name "test_all"
  "*The name of the LEGO module which inherits all other modules of the
  library."
  :type 'string
  :group 'lego)

(defpgdefault help-menu-entries
  '(["LEGO Reference Card" (browse-url lego-www-refcard) t]
    ["LEGO library (WWW)" (browse-url lego-library-www-page)  t]))

(defpgdefault menu-entries
  '(["intros" lego-intros t]
    ["Intros" lego-Intros t]
    ["Refine" lego-Refine t]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Configuration of Generic Proof Package ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Users should not need to change this.

(defvar lego-shell-handle-output
  (lambda (cmd string) 
    (when (proof-string-match "^Module" cmd)
      ;; prevent output and just give a minibuffer message
      (setq proof-shell-last-output-kind 'systemspecific)
      (message "Imports done!")))
  "Acknowledge end of processing import declarations.")

(defconst lego-process-config
  ;; da: I think "Configure AnnotateOn;" is only included here for
  ;; safety since there is a bug in LEGO which turns it off
  ;; inadvertently sometimes.
  "Init XCC; Configure PrettyOn; Configure AnnotateOn;"
  "Command to initialise the LEGO process.

Initialises empty context and prepares XCC theory.
Enables pretty printing.
Activates extended printing routines required for Proof General.")

(defconst lego-pretty-set-width "Configure PrettyWidth %s; "
  "Command to adjust the linewidth for pretty printing of the LEGO
  process.")

(defconst lego-interrupt-regexp "Interrupt.."
  "Regexp corresponding to an interrupt")

;; ----- web documentation

(defcustom lego-www-home-page "http://www.dcs.ed.ac.uk/home/lego/"
  "Lego home page URL."
  :type 'string
  :group 'lego)

(defcustom lego-www-latest-release
  "http://www.dcs.ed.ac.uk/home/lego/html/release-1.3.1/"
  "The WWW address for the latest LEGO release."
  :type 'string
  :group 'lego)

(defcustom lego-www-refcard
  (concat lego-www-latest-release "refcard.ps.gz")
  "URL for the Lego reference card."
  :type 'string
  :group 'lego)

(defcustom lego-library-www-page
  (concat lego-www-latest-release "library/library.html")
  "The HTML documentation of the LEGO library."
  :type 'string
  :group 'lego)


;; ----- lego-shell configuration options

(defvar lego-prog-name "lego"
  "*Name of program to run as lego.")

(defvar lego-shell-cd "Cd \"%s\";"
  "*Command of the inferior process to change the directory.")

(defvar lego-shell-proof-completed-regexp "\\*\\*\\* QED \\*\\*\\*"
  "*Regular expression indicating that the proof has been completed.")

(defvar lego-save-command-regexp
  (concat "^" (proof-ids-to-regexp lego-keywords-save)))
(defvar lego-goal-command-regexp
  (concat "^" (proof-ids-to-regexp lego-keywords-goal)))

(defvar lego-kill-goal-command "KillRef;")
(defvar lego-forget-id-command "Forget %s;")

(defvar lego-undoable-commands-regexp
  (proof-ids-to-regexp '("Dnf" "Refine" "Intros" "intros" "Next" "Normal"
  "Qrepl" "Claim" "For" "Repeat" "Succeed" "Fail" "Try" "Assumption"
  "UTac" "Qnify" "qnify" "andE" "andI" "exE" "exI" "orIL" "orIR" "orE" "ImpI"
  "impE" "notI" "notE" "allI" "allE" "Expand" "Induction" "Immed"
  "Invert")) "Undoable list")

;; ----- outline

(defvar lego-goal-regexp "\\?\\([0-9]+\\)")

(defvar lego-outline-regexp
  (concat "[[*]\\|"
	  (proof-ids-to-regexp
	   '("Discharge" "DischargeKeep" "Freeze" "$?Goal" "Module" "Record" "Inductive"
     "Unfreeze"))))

(defvar lego-outline-heading-end-regexp ";\\|\\*)")

(defvar lego-shell-outline-regexp lego-goal-regexp)
(defvar lego-shell-outline-heading-end-regexp lego-goal-regexp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;   Derived modes - they're here 'cos they define keymaps 'n stuff ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-derived-mode lego-shell-mode proof-shell-mode
   "lego-shell"
     "Major mode for LEGO proof scripts.

\\{lego-mode-map}"
   (lego-shell-mode-config))

(define-derived-mode lego-mode proof-mode
   "lego" nil
   (lego-mode-config))

(eval-and-compile
  (define-derived-mode lego-response-mode proof-response-mode
    "LEGOResp" nil
    (setq proof-response-font-lock-keywords lego-font-lock-terms)
    (lego-init-syntax-table)
    (proof-response-config-done)))

(define-derived-mode lego-goals-mode proof-goals-mode
  "LEGOGoals" "LEGO Proof State"
  (lego-goals-mode-config))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;   Code that's lego specific                                      ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; needs to handle Normal as well
;; it should ignore Normal TReg Normal VReg and (Normal ...)
(defun lego-count-undos (span)
  "This is how to work out what the undo commands are.
Given is the first SPAN which needs to be undone."
  (let ((ct 0) str i)
    (while span
      (setq str (span-property span 'cmd))
      (cond ((eq (span-property span 'type) 'vanilla)
	     (if (or (proof-string-match lego-undoable-commands-regexp str)
		     (and (proof-string-match "Equiv" str)
			  (not (proof-string-match "Equiv\\s +[TV]Reg" str))))
		 (setq ct (+ 1 ct))))
	    ((eq (span-property span 'type) 'pbp)
	     (setq i 0)
	     (while (< i (length str))
	       (if (= (aref str i) ?\;) (setq ct (+ 1 ct)))
	       (setq i (+ 1 i)))))
      (setq span (next-span span 'type)))
    (list (concat "Undo " (int-to-string ct) ";"))))

(defun lego-goal-command-p (span)
  "Decide whether argument is a goal or not"
  (proof-string-match lego-goal-command-regexp
		      (or (span-property span 'cmd) "")))

(defun lego-find-and-forget (span)
  (let (str ans)
    (while (and span (not ans))
      (setq str (span-property span 'cmd))

      (cond

       ((eq (span-property span 'type) 'comment))

       ((eq (span-property span 'type) 'proverproc))

       ((eq (span-property span 'type) 'goalsave)
	(unless (eq (span-property span 'name) proof-unnamed-theorem-name)
	  (setq ans (format lego-forget-id-command (span-property span 'name)))))
       ;; alternative definitions
       ((proof-string-match lego-definiendum-alternative-regexp str)
	(setq ans (format lego-forget-id-command (match-string 1 str))))
       ;; declarations
       ((proof-string-match (concat "\\`\\$?" (lego-decl-defn-regexp "[:|=]")) str)
	(let ((ids (match-string 1 str))) ; returns "a,b"
	  (proof-string-match proof-id ids)	; matches "a"
	  (setq ans (format lego-forget-id-command (match-string 1 ids)))))

       ((proof-string-match "\\`\\(Inductive\\|\\Record\\)\\s-*\\[\\s-*\\w+\\s-*:[^;]+\\`Parameters\\s-*\\[\\s-*\\(\\w+\\)\\s-*:" str)
	(setq ans (format lego-forget-id-command (match-string 2 str))))

       ((proof-string-match
	 "\\`\\(Inductive\\|Record\\)\\s-*\\[\\s-*\\(\\w+\\)\\s-*:" str)
	(setq ans
	      (format lego-forget-id-command (match-string 2 str))))

       ((proof-string-match "\\`\\s-*Module\\s-+\\(\\S-+\\)\\W" str)
	(setq ans (format "ForgetMark %s;" (match-string 1 str)))))
      ;; Carry on searching forward for something to forget
      ;; (The first thing to be forget will forget everything following)
      (setq span (next-span span 'type)))
    (when ans (list ans)))); was (or ans proof-no-command)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;   Other stuff which is required to customise script management   ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun lego-goal-hyp ()
  (cond
   ((looking-at lego-goal-regexp)
    (cons 'goal (match-string 1)))
   ((looking-at proof-shell-assumption-regexp)
    (cons 'hyp (match-string 1)))
   (t nil)))


(defun lego-state-preserving-p (cmd)
  (not (proof-string-match lego-undoable-commands-regexp cmd)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;   Commands specific to lego                                      ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(proof-defshortcut lego-Intros "Intros "  [(control I)])
(proof-defshortcut lego-intros "intros "  [(control i)])
(proof-defshortcut lego-Refine "Refine "  [(control r)])


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;   Lego shell startup and exit hooks                              ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defvar lego-shell-current-line-width nil
  "Current line width of the LEGO process's pretty printing module.
  Its value will be updated whenever the corresponding screen gets
  selected.")

;; The line width needs to be adjusted if the LEGO process is
;; running and is out of sync with the screen width

(defun lego-shell-adjust-line-width ()
  "Use LEGO's pretty printing facilities to adjust output line width.
Checks the width in the `proof-goals-buffer'"
  (and (proof-shell-live-buffer)
       (proof-with-current-buffer-if-exists proof-goals-buffer
	 (let ((current-width
		;; Actually, one might sometimes
		;; want to get the width of the proof-response-buffer
		;; instead. Never mind.
		(window-width (get-buffer-window proof-goals-buffer t))))
	   (if (equal current-width lego-shell-current-line-width) ()
	     ; else
	     (setq lego-shell-current-line-width current-width)
	     (set-buffer proof-shell-buffer)
	     (insert (format lego-pretty-set-width (- current-width 1)))
	     )))))

(defun lego-mode-config ()

  (setq proof-terminal-string ";")
  (setq proof-script-comment-start "(*")
  (setq proof-script-comment-end "*)")

  (setq proof-assistant-home-page lego-www-home-page)

  (setq proof-showproof-command "Prf;"
	proof-goal-command "Goal %s;"
	proof-save-command "Save %s;"
	proof-context-command "Ctxt;"
	proof-info-command "Help;")

  (setq proof-prog-name lego-prog-name)

  (setq proof-goal-command-p 'lego-goal-command-p
	proof-completed-proof-behaviour 'closeany ; new in 3.0
	proof-count-undos-fn 'lego-count-undos
	proof-find-and-forget-fn 'lego-find-and-forget
	pg-topterm-goalhyplit-fn 'lego-goal-hyp
	proof-state-preserving-p 'lego-state-preserving-p)

  (setq	proof-save-command-regexp lego-save-command-regexp
	proof-goal-command-regexp lego-goal-command-regexp
	proof-save-with-hole-regexp lego-save-with-hole-regexp
	proof-goal-with-hole-regexp lego-goal-with-hole-regexp
	proof-kill-goal-command lego-kill-goal-command
	proof-indent-any-regexp
	(proof-regexp-alt (proof-ids-to-regexp lego-commands) "\\s(" "\\s)"))

  (lego-init-syntax-table)

  ;; da: I've moved these out of proof-config-done in proof-script.el
  (setq pbp-goal-command "Pbp %s;")
  (setq pbp-hyp-command "PbpHyp %s;")

;; font-lock

  (set proof-script-font-lock-keywords lego-font-lock-keywords-1)

  (proof-config-done)

;; outline

  (make-local-variable 'outline-regexp)
  (setq outline-regexp lego-outline-regexp)

  (make-local-variable 'outline-heading-end-regexp)
  (setq outline-heading-end-regexp lego-outline-heading-end-regexp)

;; tags
  (cond ((boundp 'tags-table-list) ;; GNU Emacs
	 (make-local-variable 'tags-table-list)
	 (setq tags-table-list (cons lego-tags tags-table-list))))

  (and (boundp 'tag-table-alist)  ;; XEmacs
       (setq tag-table-alist
	     (append '(("\\.l$" . lego-tags)
		       ("lego"  . lego-tags))
		     tag-table-alist)))

  (set (make-local-variable 'blink-matching-paren-dont-ignore-comments) t)

;; hooks and callbacks

  (add-hook 'proof-shell-insert-hook 'lego-shell-adjust-line-width))

(defun lego-equal-module-filename (module filename)
  "Returns `t' if MODULE is equal to the FILENAME and `nil' otherwise.
The directory and extension is stripped of FILENAME before the test."
  (equal module
	 (file-name-sans-extension (file-name-nondirectory filename))))

(defun lego-shell-compute-new-files-list ()
  "Function to update `proof-included-files-list'.
Value for `proof-shell-compute-new-files-list', which see.

For LEGO, we assume that module identifiers coincide with file names."
  (let ((module (match-string 1)))
    (cdr (member-if
	  (lambda (filename) (lego-equal-module-filename module filename))
	  proof-included-files-list))))

(defun lego-shell-mode-config ()
  (setq proof-shell-cd-cmd lego-shell-cd
	proof-shell-proof-completed-regexp lego-shell-proof-completed-regexp
	proof-shell-error-regexp lego-error-regexp
	proof-shell-interrupt-regexp lego-interrupt-regexp
	proof-shell-assumption-regexp lego-id
	pg-subterm-first-special-char ?\360
	pg-subterm-start-char ?\372
	pg-subterm-sep-char ?\373
	pg-subterm-end-char ?\374
	pg-topterm-regexp "\375"
	proof-shell-eager-annotation-start "\376"
	proof-shell-eager-annotation-start-length 1
	proof-shell-eager-annotation-end "\377"
	proof-shell-annotated-prompt-regexp "Lego> \371"
	proof-shell-result-start "\372 Pbp result \373"
	proof-shell-result-end "\372 End Pbp result \373"
	proof-shell-start-goals-regexp "\372 Start of Goals \373"
	proof-shell-end-goals-regexp "\372 End of Goals \373"
	proof-shell-pre-sync-init-cmd "Configure AnnotateOn;"
	proof-shell-init-cmd lego-process-config
	proof-shell-restart-cmd lego-process-config
	pg-subterm-anns-use-stack nil
	proof-shell-handle-output-system-specific lego-shell-handle-output
	lego-shell-current-line-width nil

	;; LEGO uses Unicode escape prefix: liable to create problems
	proof-shell-unicode nil

	proof-shell-process-file
	(cons "Creating mark \"\\(.*\\)\" \\[\\(.*\\)\\]"
	  (lambda () (let ((match (match-string 2)))
		       (if (equal match "") match
			 (concat (file-name-sans-extension match) ".l")))))

	proof-shell-retract-files-regexp
	"forgot back through Mark \"\\(.*\\)\""
	
	proof-shell-font-lock-keywords lego-font-lock-keywords-1

	proof-shell-compute-new-files-list
	'lego-shell-compute-new-files-list)

  (lego-init-syntax-table)

  (proof-shell-config-done))

(defun lego-goals-mode-config ()
  (setq pg-goals-change-goal "Next %s;"
	pg-goals-error-regexp lego-error-regexp)
  (setq font-lock-keywords lego-font-lock-terms)
  (lego-init-syntax-table)
  (proof-goals-config-done))


(provide 'lego)
