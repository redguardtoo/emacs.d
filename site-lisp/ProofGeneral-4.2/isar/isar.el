;; isar.el --- Major mode for Isabelle/Isar proof assistant
;;
;; Copyright (C) 1994-2010 LFCS Edinburgh.
;;
;; License:   GPL (GNU GENERAL PUBLIC LICENSE)
;;
;; Maintainers:   David Aspinall, Makarius, Stefan Berghofer
;;
;; Authors:       David Aspinall <David.Aspinall@ed.ac.uk>
;;	          Markus Wenzel <wenzelm@in.tum.de>
;;
;; Contributors:  David von Oheimb, Sebastian Skalberg
;;
;; isar.el,v 12.1 2011/10/17 09:25:36 da Exp
;;

;;; Code:

(eval-when-compile 
  (require 'cl))

(eval-when (compile)
  (require 'span)
  (require 'proof-syntax)
  (require 'pg-goals)
  (require 'pg-vars)
  (require 'outline)
  (defvar comment-quote-nested nil)
  (defvar isar-use-find-theorems-form nil)
  (defvar isar-use-linear-undo nil)
  (proof-ready-for-assistant 'isar))	; compile for isar

(require 'proof)
(require 'isabelle-system)		; system code
(require 'isar-find-theorems)		; "Find Theorems" search form

;;
;; Load syntax
;;

(defcustom isar-keywords-name nil
  "Specifies a theory-specific keywords setting to use with Isar.
See -k option for Isabelle interface script."
  :type 'string
  :group 'isabelle)

(or (featurep 'isar-keywords)
    ;; Pickup isar-keywords file from somewhere appropriate, giving
    ;; user chance to set name of file, or based on name of logic.
    (isabelle-load-isar-keywords
     (or isar-keywords-name
	 isabelle-chosen-logic)))
(require 'isar-syntax)


;; Completion table for Isabelle/Isar identifiers
(defpgdefault completion-table isar-keywords-major)

(defcustom isar-web-page
  "http://isabelle.in.tum.de/Isar/"
  "URL of web page for Isabelle/Isar."
  :type 'string
  :group 'isabelle-isar)


;; Adjust toolbar entries (must be done before proof-toolbar is loaded).

(eval-after-load "pg-custom"
  '(setq isar-toolbar-entries
	 (assq-delete-all 'qed (assq-delete-all 'goal isar-toolbar-entries))))


(defun isar-strip-terminators ()
  "Remove explicit Isabelle/Isar command terminators `;' from the buffer."
  (interactive)
  (save-excursion
    (goto-char (point-min))
    (while (proof-search-forward ";" (point-max) t)
      (while (not (proof-buffer-syntactic-context))
	(delete-char -1)
	(or (proof-looking-at ";\\|\\s-\\|$")
	    (insert " "))))))


(defun isar-markup-ml (string)
  "Return marked up version of ML command STRING for Isar."
  (format "ML_command {* %s *};" string))


(defun isar-mode-config-set-variables ()
  "Configure generic proof scripting mode variables for Isabelle/Isar."
  (set (make-local-variable 'indent-tabs-mode) nil)
  (setq
   proof-assistant-home-page    isar-web-page
   proof-guess-command-line     'isabelle-set-prog-name
   proof-prog-name-guess	t

   ;; proof script syntax
   proof-terminal-string          ";"          ; forcibly ends a command
   proof-electric-terminator-noterminator t  ; don't insert it
   proof-script-command-start-regexp  isar-any-command-regexp 

   proof-script-integral-proofs t
   proof-script-comment-start          isar-comment-start
   proof-script-comment-end            isar-comment-end
   proof-script-comment-start-regexp   isar-comment-start-regexp
   proof-script-comment-end-regexp     isar-comment-end-regexp
   proof-string-start-regexp    isar-string-start-regexp
   proof-string-end-regexp      isar-string-end-regexp

   ;; For func-menu and finding goal..save regions
   proof-save-command-regexp    isar-save-command-regexp
   proof-goal-command-regexp    isar-goal-command-regexp
   proof-goal-with-hole-regexp  isar-named-entity-regexp
   proof-goal-with-hole-result	isar-named-entity-name-match-number
   proof-save-with-hole-regexp  nil
   proof-script-imenu-generic-expression isar-generic-expression
   imenu-syntax-alist isar-script-syntax-table-alist

   proof-indent-enclose-offset  (- proof-indent)
   proof-indent-open-offset     0
   proof-indent-close-offset    0
   proof-indent-any-regexp      isar-indent-any-regexp
;   proof-indent-inner-regexp    isar-indent-inner-regexp
   proof-indent-enclose-regexp  isar-indent-enclose-regexp
   proof-indent-open-regexp     isar-indent-open-regexp
   proof-indent-close-regexp    isar-indent-close-regexp

   ;; proof engine
   proof-showproof-command      "pr"
   proof-goal-command           "lemma \"%s\""
   proof-save-command           "qed"
   proof-context-command        "print_context"
   proof-info-command           "welcome"
   proof-query-identifier-command
   '((nil     "thm %s;")
     (string  "term \"%s\";")
     (comment "term \"%s\";"))
   proof-shell-start-silent-cmd "disable_pr"
   proof-shell-stop-silent-cmd  "enable_pr"
   proof-shell-trace-output-regexp  "\^AI\^AV"
   proof-script-preprocess      'isar-command-wrapping
   ;; command hooks
   proof-goal-command-p         'isar-goal-command-p
   proof-really-save-command-p  'isar-global-save-command-p
   proof-state-preserving-p     'isar-state-preserving-p
   proof-shell-compute-new-files-list 'isar-shell-compute-new-files-list
   ;; span menu
   proof-script-span-context-menu-extensions 'isabelle-create-span-menu)
  ;; proof assistant settings
  (setq proof-use-pgip-askprefs	t)
  ;; others: find theorems, undo config
  (isar-configure-from-settings))

(defun isar-shell-mode-config-set-variables ()
  "Configure generic proof shell mode variables for Isabelle/Isar."
  (setq

   proof-shell-annotated-prompt-regexp  "^\\w*[>#] \^AS"

   ;; for issuing command, not used to track cwd in any way.
   proof-shell-cd-cmd		(isar-markup-ml "ThyLoad.add_path \"%s\"")

   ;; Escapes for filenames inside ML strings.
   ;; We also make a hack for a bug in Isabelle, by switching from
   ;; backslashes to forward slashes if it looks like we're running
   ;; on Windows.
   proof-shell-filename-escapes
   (if (fboundp 'win32-long-filename)   ; rough test for XEmacs on win32
       ;; Patterns to unixfy names.
       ;; Jacques Fleuriot's patch in ML does this too: ("^[a-zA-Z]:" . "")
       ;; But I'll risk leaving drive names in, not sure how to replace them.
       '(("\\\\" . "/") ("\"" . "\\\""))
     ;; Normal case: quotation for backslash, quote mark.
     '(("\\\\" . "\\\\") ("\""   . "\\\"")))

   proof-shell-interrupt-regexp         "\^AM\\*\\*\\* Interrupt"
   proof-shell-error-regexp             "\^AM\\*\\*\\*"
   proof-shell-proof-completed-regexp   nil     ; n.a.

   pg-next-error-regexp	  "\\((line \\([0-9]+\\) of \"[^\"]+\")\\)"
   pg-next-error-filename-regexp "\\((line [0-9]+ of \"\\([^\"]+\\)\")\\)"

   ;; matches names of assumptions
   proof-shell-assumption-regexp        isar-id

   proof-shell-start-goals-regexp       "\^AO"
   proof-shell-end-goals-regexp         "\^AP"

   proof-shell-init-cmd			nil
   proof-shell-restart-cmd              "ProofGeneral.restart"

   proof-shell-eager-annotation-start-length 2
   proof-shell-eager-annotation-start   "\^AI\\|\^AK"
   proof-shell-eager-annotation-end     "\^AJ\\|\^AL"
   proof-shell-strip-output-markup	'isar-strip-output-markup

   pg-special-char-regexp               "\^A[0-9A-Z]"
   pg-subterm-help-cmd			"term %s"
   proof-cannot-reopen-processed-files  t

   ;; Urgent messages delimited by eager annotations
   proof-shell-clear-response-regexp    
   "\^AIProof General, please clear the response buffer."
   proof-shell-clear-goals-regexp       
   "\^AIProof General, please clear the goals buffer."
   proof-shell-theorem-dependency-list-regexp 
   "\^AIProof General, theorem dependencies of \"\\(.*\\)\" are \"\\(.*\\)\"\\(\^AJ\\)"
   proof-shell-retract-files-regexp
   "\^AIProof General, you can unlock the file \"\\(.*\\)\"\^AJ"
   proof-shell-process-file
   (cons
    "\^AIProof General, this file is loaded: \"\\(.*\\)\"\^AJ"
    (lambda () (match-string 1)))

   proof-shell-match-pgip-cmd		"\^AI<pgip"
   proof-shell-issue-pgip-cmd		'isabelle-process-pgip

   proof-shell-theorem-dependency-list-split "\" \""
   proof-shell-show-dependency-cmd	"thm %s;"

   proof-shell-compute-new-files-list 'isar-shell-compute-new-files-list
   proof-shell-inform-file-processed-cmd 
   "ProofGeneral.inform_file_processed \"%s\""
   proof-shell-inform-file-retracted-cmd 
   "ProofGeneral.inform_file_retracted \"%s\""))


;;
;; Settings for the interface
;;
;; Note: settings for Isabelle are configured automatically via PGIP messages,
;; see `pg-pgip-process-hasprefs' in pg-pgip.el and 
;; `proof-assistant-settings-cmds' in proof-menu.el.
;;

(defun isar-set-proof-find-theorems-command ()
  (setq proof-find-theorems-command
	(if isar-use-find-theorems-form
	    'isar-find-theorems-form
	  'isar-find-theorems-minibuffer)))

(defpacustom use-find-theorems-form nil
  "Use a form-style input for the find theorems operation."
  :type 'boolean
  :eval (isar-set-proof-find-theorems-command))

(defun isar-set-undo-commands (&optional initp)
  (unless initp
    (proof-deactivate-scripting)
    (when proof-script-buffer
      (message "Warning: switching undo mechanism will break undo in current buffer")))
  (setq proof-count-undos-fn 'isar-count-undos)
  (when isar-use-linear-undo
    (setq proof-kill-goal-command nil)
    (setq proof-find-and-forget-fn 'isar-count-undos)
    (setq proof-arbitrary-undo-positions t))
  (when (not isar-use-linear-undo)
    (setq proof-kill-goal-command "ProofGeneral.kill_proof")
    (setq proof-find-and-forget-fn 'isar-find-and-forget)
    (setq proof-arbitrary-undo-positions nil)))

(defpacustom use-linear-undo t
  "Whether to allow undo to re-enter completed proofs (requires restart)."
  :type 'boolean
  :eval (isar-set-undo-commands))

(defun isar-configure-from-settings ()
  (isar-set-proof-find-theorems-command)
  (isar-set-undo-commands 'init))

;;
;; Theory loader operations
;;

(defun isar-remove-file (name files cmp-base)
  (let (result)
    (while files
      (let*
	  ((file (car files))
	   (same (if cmp-base (string= name (file-name-nondirectory file))
		   (string= name file))))
	(unless same 
	  (setq result (cons file result)))
	(setq files (cdr files))))
    result))

(defun isar-shell-compute-new-files-list ()
  "Compute the new list of files read by the proof assistant.
This is called when Proof General spots output matching
`proof-shell-retract-files-regexp'."
  (let*
      ((name (match-string 1))
       (base-name (file-name-nondirectory name)))
    (if (string= name base-name)
	(isar-remove-file name proof-included-files-list t)
      (isar-remove-file 
       (file-truename name) proof-included-files-list nil))))


;;
;; Define the derived modes
;;
;; use eval-and-compile to define vars for byte comp.

(eval-and-compile
(define-derived-mode isar-shell-mode proof-shell-mode
   "Isabelle Shell" nil
   (isar-shell-mode-config)))

(eval-and-compile
(define-derived-mode isar-response-mode proof-response-mode
  "Isar Messages" nil
  (isar-response-mode-config)))

(eval-and-compile
(define-derived-mode isar-goals-mode proof-goals-mode
  "Isar Proofstate" nil
  (isar-goals-mode-config)))

(eval-and-compile
(define-derived-mode isar-mode proof-mode
  "Isar"
  "Major mode for editing Isar proof scripts.

\\{isar-mode-map}"
  (isar-mode-config)))



;;
;; Help menu
;;
;; NB: definvisible must be after derived modes (uses isar-mode-map)

(proof-definvisible isar-help-antiquotations "print_antiquotations" "hA")
(proof-definvisible isar-help-attributes "print_attributes" "ha")
(proof-definvisible isar-help-cases "print_cases" "hc")
(proof-definvisible isar-help-claset "print_claset" "hC")
(proof-definvisible isar-help-commands "print_commands" "ho")
(proof-definvisible isar-help-facts "print_facts" "hf")
(proof-definvisible isar-help-syntax "print_syntax" "hi")
(proof-definvisible isar-help-induct-rules "print_induct_rules" "hI")
(proof-definvisible isar-help-methods "print_methods" "hm")
(proof-definvisible isar-help-simpset "print_simpset" "hS")
(proof-definvisible isar-help-binds "print_binds" "hb")
(proof-definvisible isar-help-theorems "print_theorems" "ht")
(proof-definvisible isar-help-trans-rules "print_trans_rules" "hT")

;;
;; Command menu
;;

(proof-definvisible isar-cmd-display-draft
 '(progn
    (proof-save-this-buffer)
    (format "display_drafts \"%s\"" buffer-file-name))
 [(control d)])

(proof-definvisible isar-cmd-print-draft
  '(if (y-or-n-p
	(format "Print draft of file %s? " buffer-file-name))
       (progn
	 (proof-save-this-buffer)
	 (format "print_drafts \"%s\"" buffer-file-name))
     (error "Aborted"))
  [(control p)])

(proof-definvisible isar-cmd-quickcheck "quickcheck" [(control q)])
(proof-definvisible isar-cmd-nitpick "nitpick" [(control n)])
(proof-definvisible isar-cmd-refute "refute" "r")
(proof-definvisible isar-cmd-sledgehammer "sledgehammer" [(control s)])

(defpgdefault menu-entries
  (append
   (list isabelle-logics-menu-entries)
   (list
    (cons "Commands"
	  (list
	   ["Quickcheck"         isar-cmd-quickcheck     t]
	   ["Nitpick"            isar-cmd-nitpick        t]
	   ["Refute"             isar-cmd-refute         t]
	   ["Sledgehammer"       isar-cmd-sledgehammer   t]
	   ["Display Draft"	 isar-cmd-display-draft  t]
	   ["Print Draft"	 isar-cmd-print-draft    t])))
   (list
    (cons "Show Me"
	  (list
	   ["Cases"              isar-help-cases          t]
	   ["Facts"              isar-help-facts          t]
	   ["Term Bindings"      isar-help-binds          t]
	   "----"
	   ["Classical Rules"    isar-help-claset         t]
	   ["Induct/Cases Rules" isar-help-induct-rules   t]
	   ["Simplifier Rules"   isar-help-simpset        t]
	   ["Theorems"           isar-help-theorems       t]
	   ["Transitivity Rules" isar-help-trans-rules    t]
	   "----"
	   ["Antiquotations"     isar-help-antiquotations t]
	   ["Attributes"         isar-help-attributes     t]
	   ["Commands"           isar-help-commands       t]
	   ["Inner Syntax"       isar-help-syntax         t]
	   ["Methods"            isar-help-methods        t])))))

(defun isar-set-command ()
  "Query the user to set the command to run Isabelle"
  (interactive)
  (isa-set-isabelle-command t))

(defpgdefault help-menu-entries isabelle-docs-menu)

;; undo proof commands
(defun isar-count-undos (span)
  "Return commands to be used to forget SPAN."
  (let ((ct 0) str i)
    (while span
      (setq str (or (span-property span 'cmd) ""))
      (cond ((or (eq (span-property span 'type) 'vanilla)
		 (eq (span-property span 'type) 'goalsave))
	     (or (proof-string-match isar-undo-skip-regexp str)
		 (proof-string-match isar-undo-ignore-regexp str)
		 (setq ct (+ 1 ct))))
	    ((eq (span-property span 'type) 'pbp)
	     ;; this case for automatically inserted text (e.g. sledgehammer)
	     (cond ((not (proof-string-match isar-undo-skip-regexp str))
		    (setq ct 1)
		    (setq i 0)
		    ;; If we find a semicolon, assume several commands,
		    ;; and increment the undo count.
		    (while (< i (length str))
		      (if (= (aref str i) ?\;)
			  (setq ct (+ 1 ct)))
		      (setq i (+ 1 i))))
		   (t nil))))
      (setq span (next-span span 'type)))
    (list (isar-undos isar-use-linear-undo ct))))

;; undo theory commands
(defun isar-find-and-forget (span)
  "Return commands to be used to forget SPAN."
  (let (str ans answers)
    (while span
      (setq str (span-property span 'cmd))
      (setq ans nil)
      (cond
       ;; comment, diagnostic, nested proof command: skip
       ;; FIXME: should adjust proof-nesting-depth here.
       ((or (eq (span-property span 'type) 'comment)
	    (eq (span-property span 'type) 'proverproc)
	    (eq (span-property span 'type) 'proof)
	    (and str (proof-string-match isar-undo-skip-regexp str))
	    (and str (proof-string-match isar-undo-ignore-regexp str))))
       ;; finished goal: undo
       ((eq (span-property span 'type) 'goalsave)
	(setq ans isar-undo))
       ;; open goal: skip and exit
       ((and str (proof-string-match isar-goal-command-regexp str))
	(setq span nil))
       ;; control command: cannot undo
       ((and str (proof-string-match isar-undo-fail-regexp str))
	(setq ans (isar-cannot-undo (match-string 1 str)))
	(setq answers nil)
	(setq span nil))
       ;; theory: remove and exit
       ((and str (proof-string-match isar-undo-remove-regexp str))
	(setq ans (isar-remove (match-string 3 str)))
	(setq span nil))
       ;; else: undo
       (t
	(setq ans isar-undo)))
      (if ans (setq answers (cons ans answers)))
      (if span (setq span (next-span span 'type))))
    answers))

(defun isar-goal-command-p (span)
  "Decide whether argument SPAN is a goal or not."
  (proof-string-match isar-goal-command-regexp
		      (or (span-property span 'cmd) "")))

(defun isar-global-save-command-p (span str)
  "Decide whether argument SPAN with command STR is a global save command."
  (or
   (proof-string-match isar-global-save-command-regexp str)
   (let ((ans nil) (lev 0) cmd)
     (while (and (not ans) span (setq span (prev-span span 'type)))
       (setq cmd (or (span-property span 'cmd) ""))
       (cond
	;; comment: skip
	((eq (span-property span 'type) 'comment))
	;; local qed: enter block
	((proof-string-match isar-save-command-regexp cmd)
	 (setq lev (+ lev 1)))
	;; local goal: leave block, or done
	((proof-string-match isar-local-goal-command-regexp cmd)
	 (if (> lev 0) (setq lev (- lev 1)) (setq ans 'no)))
	;; global goal: done
	((proof-string-match isar-goal-command-regexp cmd)
	 (setq ans 'yes))))
     (eq ans 'yes))))

(defvar isar-current-goal 1
  "Last goal that Emacs looked at.")

(defun isar-state-preserving-p (cmd)
  "Non-nil if command CMD preserves the proofstate."
  (proof-string-match isar-undo-skip-regexp cmd))


;;
;; Commands specific to isar
;;

(proof-defshortcut isar-bold      "\\<^bold>%p" [(control b)])
(proof-defshortcut isar-local     "\\<^loc>%p" [(control c)])
(proof-defshortcut isar-super     "\\<^sup>%p" [(control u)])
(proof-defshortcut isar-sub       "\\<^sub>%p" [(control l)])
(proof-defshortcut isar-longsuper "\\<^bsup>%p\\<^esup>" [?u])
(proof-defshortcut isar-longsub   "\\<^bsub>%p\\<^esub>" [?l])
(proof-defshortcut isar-idsub     "\\<^isub>%p" [(control i)])
(proof-defshortcut isar-raw       "\\<^raw:%p>" [(control r)])
(proof-defshortcut isar-antiquote "@{text \"%p\"}" [(control a)])
(proof-defshortcut isar-ml	  "ML {* %p *}" [(control x)])


;;
;; Isar shell startup and exit hooks
;;

(defvar isar-shell-current-line-width nil
  "Current line width of the Isabelle process's pretty printing module.
Its value will be updated whenever the corresponding screen gets
selected.")

(defun isar-shell-adjust-line-width ()
  "Use Isabelle's pretty printing facilities to adjust output line width.
Checks the width in the `proof-goals-buffer'"
  (let ((ans ""))
    (and (not proof-shell-silent)
	 (proof-with-current-buffer-if-exists proof-goals-buffer
	   (let ((current-width
		  ;; Actually, one might want the width of the
		  ;; proof-response-buffer instead. Never mind.
		  (max 20 (window-width
			   (get-buffer-window proof-goals-buffer t)))))

	     (if (equal current-width isar-shell-current-line-width) ()
	       (setq isar-shell-current-line-width current-width)
	       (set-buffer proof-shell-buffer)
	       (setq ans (format "pretty_setmargin %d;"
				 (- current-width 4)))))))
    ans))

;;
;; Shell mode command adjusting
;;

(defsubst isar-string-wrapping (string)
  (concat
   "\""
   (replace-regexp-in-string
    "[\000-\037\"\\\\]"
    (lambda (str) (format "\\\\%03d" (string-to-char str)))
    string)
   "\""))

(defsubst isar-positions-of (filename start end)
  (let ((line (line-number-at-pos start)))
    (format "(\"file\"=%s, \"line\"=\"%d\") "
	     (isar-string-wrapping filename) ; cache this?
	     line)))

(defcustom isar-wrap-commands-singly t
  "Non-nil to use command wrapping around commands sent to Isabelle.
This slows down interactive processing slightly."
  :type 'boolean
  :group 'isabelle)

(defun isar-command-wrapping (filename start end string)
  "A value for `proof-script-preprocess'."
  (if isar-wrap-commands-singly
      (list "Isabelle.command "
	    (isar-positions-of filename start end)
	    (isar-string-wrapping string))
    (list (replace-regexp-in-string "\n" "\\\\<^newline>" string))))

(defun isar-preprocessing ()
  "Insert sync markers and other hacks.
Uses variables `string' and `scriptspan' passed by dynamic scoping."
  (with-no-warnings  ; dynamic scoping of string, scriptspan
    (if (proof-string-match isabelle-verbatim-regexp string)
	(setq string (match-string 1 string))
      (unless (string-match ";[ \t]*\\'" string)
	(setq string (concat string ";")))
      (setq string (concat
		    "\\<^sync>; "
		    (isar-shell-adjust-line-width)
		    string
		    " \\<^sync>;")))))

;;
;;   Configuring proof output buffer
;;

(defun isar-mode-config ()
  (isar-mode-config-set-variables)
  (isar-init-syntax-table)
  (setq proof-script-font-lock-keywords isar-font-lock-keywords-1)
  (set (make-local-variable 'comment-quote-nested) nil) ;; can cope with nested comments
  (set (make-local-variable 'outline-regexp) isar-outline-regexp)
  (set (make-local-variable 'outline-heading-end-regexp) 
       isar-outline-heading-end-regexp)
  (set (make-local-variable 'outline-heading-alist)
       isar-outline-heading-alist)
  (set (make-local-variable 'blink-matching-paren-dont-ignore-comments) t)
  (add-hook 'proof-shell-insert-hook 'isar-preprocessing)
  (proof-config-done))

(defun isar-shell-mode-config ()
  "Configure Proof General proof shell for Isabelle/Isar."
  (isar-init-output-syntax-table)
  (isar-shell-mode-config-set-variables)
  (set (make-local-variable 'font-lock-extra-managed-props)
       '(invisible))
  (setq proof-shell-font-lock-keywords
	isar-shell-font-lock-keywords)
  (proof-shell-config-done))

(defun isar-response-mode-config ()
  (isar-init-output-syntax-table)
  (setq proof-response-font-lock-keywords
	(append proof-response-font-lock-keywords
		isar-output-font-lock-keywords-1))
  (setq font-lock-multiline t)
  (make-local-variable 'jit-lock-chunk-size)
  (setq jit-lock-chunk-size 2000)
  (proof-response-config-done))

(defun isar-goals-mode-config ()
  (setq pg-goals-change-goal "prefer %s")
  (setq pg-goals-error-regexp proof-shell-error-regexp)
  (isar-init-output-syntax-table)
  (setq proof-goals-font-lock-keywords
	(append proof-goals-font-lock-keywords
		isar-goals-font-lock-keywords))
  (setq font-lock-multiline t)
  (make-local-variable 'jit-lock-chunk-size)
  (setq jit-lock-chunk-size 2000)
  (proof-goals-config-done))

(provide 'isar)

;;; isar.el ends here
