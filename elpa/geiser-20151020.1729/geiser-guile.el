;; geiser-guile.el -- guile's implementation of the geiser protocols

;; Copyright (C) 2009, 2010, 2011, 2012, 2013, 2014, 2015 Jose Antonio Ortega Ruiz

;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the Modified BSD License. You should
;; have received a copy of the license along with this program. If
;; not, see <http://www.xfree86.org/3.3.6/COPYRIGHT2.html#5>.

;; Start date: Sun Mar 08, 2009 23:03



(require 'geiser-connection)
(require 'geiser-syntax)
(require 'geiser-custom)
(require 'geiser-base)
(require 'geiser-eval)
(require 'geiser-edit)
(require 'geiser-log)
(require 'geiser)

(require 'compile)
(require 'info-look)

(eval-when-compile (require 'cl))


;;; Customization:

(defgroup geiser-guile nil
  "Customization for Geiser's Guile flavour."
  :group 'geiser)

(geiser-custom--defcustom geiser-guile-binary
  (cond ((eq system-type 'windows-nt) "guile.exe")
        ((eq system-type 'darwin) "guile")
        (t "guile"))
  "Name to use to call the Guile executable when starting a REPL."
  :type '(choice string (repeat string))
  :group 'geiser-guile)

(geiser-custom--defcustom geiser-guile-load-path nil
  "A list of paths to be added to Guile's load path when it's
started."
  :type '(repeat file)
  :group 'geiser-guile)

(geiser-custom--defcustom geiser-guile-init-file "~/.guile-geiser"
  "Initialization file with user code for the Guile REPL.
If all you want is to load ~/.guile, set
`geiser-guile-load-init-file-p' instead."
  :type 'string
  :group 'geiser-guile)

(geiser-custom--defcustom geiser-guile-load-init-file-p nil
  "Whether to load ~/.guile when starting Guile.
Note that, due to peculiarities in the way Guile loads its init
file, using `geiser-guile-init-file' is not equivalent to setting
this variable to t."
  :type 'boolean
  :group 'geiser-guile)

(geiser-custom--defcustom geiser-guile-debug-show-bt-p nil
  "Whether to autmatically show a full backtrace when entering the debugger.
If `nil', only the last frame is shown."
  :type 'boolean
  :group 'geiser-guile)

(geiser-custom--defcustom geiser-guile-jump-on-debug-p nil
  "Whether to autmatically jump to error when entering the debugger.
If `t', Geiser will use `next-error' to jump to the error's location."
  :type 'boolean
  :group 'geiser-guile)

(geiser-custom--defcustom geiser-guile-show-debug-help-p t
  "Whether to show brief help in the echo area when entering the debugger."
  :type 'boolean
  :group 'geiser-guile)

(geiser-custom--defcustom geiser-guile-warning-level 'medium
  "Verbosity of the warnings reported by Guile.

You can either choose one of the predefined warning sets, or
provide a list of symbols identifying the ones you want. Possible
choices are arity-mismatch, unbound-variable, unused-variable and
unused-toplevel. Unrecognised symbols are ignored.

The predefined levels are:

  - Medium: arity-mismatch, unbound-variable, format
  - High: arity-mismatch, unbound-variable, unused-variable, format
  - None: no warnings

Changes to the value of this variable will automatically take
effect on new REPLs. For existing ones, use the command
\\[geiser-guile-update-warning-level]."
  :type '(choice (const :tag "Medium (arity and unbound vars)" medium)
                 (const :tag "High (also unused vars)" high)
                 (const :tag "No warnings" none)
                 (repeat :tag "Custom" symbol))
  :group 'geiser-guile)

(geiser-custom--defcustom geiser-guile-extra-keywords nil
  "Extra keywords highlighted in Guile scheme buffers."
  :type '(repeat string)
  :group 'geiser-guile)

(geiser-custom--defcustom geiser-guile-case-sensitive-p t
  "Non-nil means keyword highlighting is case-sensitive."
  :type 'boolean
  :group 'geiser-guile)

(geiser-custom--defcustom geiser-guile-manual-lookup-other-window-p nil
  "Non-nil means pop up the Info buffer in another window."
  :type 'boolean
  :group 'geiser-guile)

(geiser-custom--defcustom geiser-guile-manual-lookup-nodes
                          '("Guile" "guile-2.0")
  "List of info nodes that, when present, are used for manual lookups"
  :type '(repeat string)
  :group 'geiser-guile)


;;; REPL support:

(defun geiser-guile--binary ()
  (if (listp geiser-guile-binary)
      (car geiser-guile-binary)
    geiser-guile-binary))

(defun geiser-guile--parameters ()
  "Return a list with all parameters needed to start Guile.
This function uses `geiser-guile-init-file' if it exists."
  (let ((init-file (and (stringp geiser-guile-init-file)
                        (expand-file-name geiser-guile-init-file)))
        (q-flags (and (not geiser-guile-load-init-file-p) '("-q"))))
  `(,@(and (listp geiser-guile-binary) (cdr geiser-guile-binary))
    ,@q-flags "-L" ,(expand-file-name "guile/" geiser-scheme-dir)
    ,@(apply 'append (mapcar (lambda (p) (list "-L" p))
                             geiser-guile-load-path))
    ,@(and init-file (file-readable-p init-file) (list "-l" init-file)))))

;;(defconst geiser-guile--prompt-regexp "^[^() \n]+@([^)]*?)> ")
(defconst geiser-guile--prompt-regexp "[^@()]+@([^)]*?)> ")
(defconst geiser-guile--debugger-prompt-regexp
  "[^@()]+@([^)]*?) \\[[0-9]+\\]> ")


;;; Evaluation support:
(defsubst geiser-guile--linearize-args (args)
  (mapconcat 'identity args " "))

(defun geiser-guile--geiser-procedure (proc &rest args)
  (case proc
    ((eval compile) (format ",geiser-eval %s %s%s"
                            (or (car args) "#f")
                            (geiser-guile--linearize-args (cdr args))
                            (if (cddr args) "" " ()")))
    ((load-file compile-file) (format ",geiser-load-file %s" (car args)))
    ((no-values) ",geiser-no-values")
    (t (format "ge:%s (%s)" proc (geiser-guile--linearize-args args)))))

(defconst geiser-guile--module-re
  "(define-module +\\(([^)]+)\\)")

(defconst geiser-guile--library-re
  "(library +\\(([^)]+)\\)")

(defun geiser-guile--get-module (&optional module)
  (cond ((null module)
         (save-excursion
           (geiser-syntax--pop-to-top)
           (if (or (re-search-backward geiser-guile--module-re nil t)
                   (looking-at geiser-guile--library-re)
                   (re-search-forward geiser-guile--module-re nil t))
               (geiser-guile--get-module (match-string-no-properties 1))
             :f)))
        ((listp module) module)
        ((stringp module)
         (condition-case nil
             (car (geiser-syntax--read-from-string module))
           (error :f)))
        (t :f)))

(defun geiser-guile--module-cmd (module fmt &optional def)
  (when module
    (let* ((module (geiser-guile--get-module module))
           (module (cond ((or (null module) (eq module :f)) def)
                         (t (format "%s" module)))))
      (and module (format fmt module)))))

(defun geiser-guile--import-command (module)
  (geiser-guile--module-cmd module ",use %s"))

(defun geiser-guile--enter-command (module)
  (geiser-guile--module-cmd module ",m %s" "(guile-user)"))


(defun geiser-guile--exit-command () ",q")

(defun geiser-guile--symbol-begin (module)
  (if module
      (max (save-excursion (beginning-of-line) (point))
           (save-excursion (skip-syntax-backward "^(>") (1- (point))))
    (save-excursion (skip-syntax-backward "^'-()>") (point))))


;;; Error display

(defun geiser-guile--enter-debugger ()
  (let ((bt-cmd (format ",geiser-newline\n,error-message\n,%s\n"
                        (if geiser-guile-debug-show-bt-p "bt" "fr"))))
    (compilation-forget-errors)
    (goto-char (point-max))
    (geiser-repl--prepare-send)
    (comint-send-string nil bt-cmd)
    (when geiser-guile-show-debug-help-p
      (message "Debug REPL. Enter ,q to quit, ,h for help."))
    (when geiser-guile-jump-on-debug-p
      (accept-process-output (get-buffer-process (current-buffer))
                             0.2 nil t)
      (ignore-errors (next-error)))))

(defun geiser-guile--display-error (module key msg)
  (newline)
  (when (stringp msg)
    (save-excursion (insert msg))
    (geiser-edit--buttonize-files))
  (and (not key) msg (not (zerop (length msg)))))


;;; Trying to ascertain whether a buffer is Guile Scheme:

(defconst geiser-guile--guess-re
  (format "\\(%s\\|#! *.+\\(/\\| \\)guile\\( *\\\\\\)?\\)"
          geiser-guile--module-re))

(defun geiser-guile--guess ()
  (save-excursion
    (goto-char (point-min))
    (re-search-forward geiser-guile--guess-re nil t)))


;;; Keywords and syntax

(defconst geiser-guile--builtin-keywords
  '("call-with-input-file"
    "call-with-input-string"
    "call-with-output-file"
    "call-with-output-string"
    "call-with-prompt"
    "call-with-trace"
    "define-accessor"
    "define-class"
    "define-enumeration"
    "define-inlinable"
    "define-syntax-parameter"
    "eval-when"
    "lambda*"
    "syntax-parameterize"
    "use-modules"
    "with-error-to-file"
    "with-error-to-port"
    "with-error-to-string"
    "with-fluid*"
    "with-fluids"
    "with-fluids*"
    "with-input-from-port"
    "with-input-from-string"
    "with-output-to-port"
    "with-output-to-string"))

(defun geiser-guile--keywords ()
  (append
   (geiser-syntax--simple-keywords geiser-guile-extra-keywords)
   (geiser-syntax--simple-keywords geiser-guile--builtin-keywords)
   `((,(rx "(" (group "define-once") eow (* space) (? (group (+ word))))
       (1 font-lock-keyword-face)
       (2 font-lock-variable-name-face nil t))
     ("(\\(define-module\\) +(\\([^)]+\\))"
      (1 font-lock-keyword-face)
      (2 font-lock-type-face nil t)))))

(geiser-syntax--scheme-indent
 (c-declare 0)
 (c-lambda 2)
 (call-with-input-string 1)
 (call-with-output-string 0)
 (call-with-prompt 1)
 (call-with-trace 0)
 (eval-when 1)
 (lambda* 1)
 (pmatch defun)
 (sigaction 1)
 (syntax-parameterize 1)
 (with-error-to-file 1)
 (with-error-to-port 1)
 (with-error-to-string 0)
 (with-fluid* 1)
 (with-fluids 1)
 (with-fluids* 1)
 (with-input-from-string 1)
 (with-method 1)
 (with-mutex 1)
 (with-output-to-string 0)
 (with-throw-handler 1))


;;; Compilation shell regexps

(defconst geiser-guile--path-rx "^In \\([^:\n ]+\\):\n")

(defconst geiser-guile--rel-path-rx "^In +\\([^/\n :]+\\):\n")

(defvar geiser-guile--file-cache (make-hash-table :test 'equal))

(defun geiser-guile--resolve-file (file)
  (when (and (stringp file)
             (not (member file '("socket" "stdin" "unknown file"))))
    (if (file-name-absolute-p file) file
      (or (gethash file geiser-guile--file-cache)
          (puthash file
                   (geiser-eval--send/result `(:eval (:ge find-file ,file)))
                   geiser-guile--file-cache)))))

(defun geiser-guile--resolve-file-x ()
  (let ((f (geiser-guile--resolve-file (match-string-no-properties 1))))
    (and (stringp f) (list f))))


;;; REPL startup

(defconst geiser-guile-minimum-version "2.0")

(defun geiser-guile--version (binary)
  (shell-command-to-string
   (format "%s  -c %s" binary (shell-quote-argument "(display (version))"))))

(defun geiser-guile-update-warning-level ()
  "Update the warning level used by the REPL.
The new level is set using the value of `geiser-guile-warning-level'."
  (interactive)
  (let ((code `(:eval (:ge set-warnings ',geiser-guile-warning-level)
                      (geiser evaluation))))
    (geiser-eval--send/result code)))

(defun connect-to-guile ()
  "Start a Guile REPL connected to a remote process.

Start the external Guile process with the flag --listen to make
it spawn a server thread."
  (interactive)
  (geiser-connect 'guile))

(defun geiser-guile--set-geiser-load-path ()
  (let* ((path (expand-file-name "guile/" geiser-scheme-dir))
         (witness "geiser/emacs.scm")
         (code `(begin (if (not (%search-load-path ,witness))
                           (set! %load-path (cons ,path %load-path)))
                       'done)))
    (geiser-eval--send/wait code)))

(defun geiser-guile--startup (remote)
  (set (make-local-variable 'compilation-error-regexp-alist)
       `((,geiser-guile--path-rx geiser-guile--resolve-file-x)
         ("^  +\\([0-9]+\\):\\([0-9]+\\)" nil 1 2)))
  (compilation-setup t)
  (font-lock-add-keywords nil `((,geiser-guile--path-rx
                                 1 compilation-error-face)))
  (let ((geiser-log-verbose-p t))
    (when remote (geiser-guile--set-geiser-load-path))
    (geiser-eval--send/wait ",use (geiser emacs)\n'done")
    (dolist (dir geiser-guile-load-path)
      (let ((dir (expand-file-name dir)))
        (geiser-eval--send/wait `(:eval (:ge add-to-load-path ,dir)))))
    (geiser-guile-update-warning-level)))


;;; Manual lookup

(defun geiser-guile--info-spec (&optional nodes)
  (let* ((nrx "^[ 	]+-+ [^:]+:[ 	]*")
         (drx "\\b")
         (res (when (Info-find-file "r5rs" t)
                `(("(r5rs)Index" nil ,nrx ,drx)))))
    (dolist (node (or nodes geiser-guile-manual-lookup-nodes) res)
      (when (Info-find-file node t)
        (mapc (lambda (idx)
                (add-to-list 'res
                             (list (format "(%s)%s" node idx) nil nrx drx)))
              '("Variable Index" "Procedure Index" "R5RS Index"))))))


(info-lookup-add-help :topic 'symbol :mode 'geiser-guile-mode
                      :ignore-case nil
                      :regexp "[^()`',\" 	\n]+"
                      :doc-spec (geiser-guile--info-spec))

(defun guile--manual-look-up (id mod)
  (let ((info-lookup-other-window-flag
         geiser-guile-manual-lookup-other-window-p))
    (info-lookup-symbol id 'geiser-guile-mode))
  (when geiser-guile-manual-lookup-other-window-p
    (switch-to-buffer-other-window "*info*"))
  (search-forward (format "%s" id) nil t))



;;; Implementation definition:

(define-geiser-implementation guile
  (binary geiser-guile--binary)
  (arglist geiser-guile--parameters)
  (version-command geiser-guile--version)
  (minimum-version geiser-guile-minimum-version)
  (repl-startup geiser-guile--startup)
  (prompt-regexp geiser-guile--prompt-regexp)
  (debugger-prompt-regexp geiser-guile--debugger-prompt-regexp)
  (enter-debugger geiser-guile--enter-debugger)
  (marshall-procedure geiser-guile--geiser-procedure)
  (find-module geiser-guile--get-module)
  (enter-command geiser-guile--enter-command)
  (exit-command geiser-guile--exit-command)
  (import-command geiser-guile--import-command)
  (find-symbol-begin geiser-guile--symbol-begin)
  (display-error geiser-guile--display-error)
  (external-help guile--manual-look-up)
  (check-buffer geiser-guile--guess)
  (keywords geiser-guile--keywords)
  (case-sensitive geiser-guile-case-sensitive-p))

(geiser-impl--add-to-alist 'regexp "\\.scm$" 'guile t)


(provide 'geiser-guile)
