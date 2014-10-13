;;; pg-pamacs.el --- Macros for per-proof assistant configuration
;;
;; Copyright (C) 2010, 2011  LFCS Edinburgh, David Aspinall.
;;
;; Author: David Aspinall <da@longitude>
;; Keywords: internal

;;; Commentary:
;;
;; Macros for defining per-assistant customization settings.
;;
;; This mechanism is an improved way to handle per-assistant settings.
;; Instead of declaring a variable "proof-assistant-web-page" and
;; duplicating it in the prover specific code to make the generic
;; setting, we automatically declare "isabelle-web-page",
;; "coq-web-page", etc, using these macros.
;;
;; The advantage of this is that people's save settings will work
;; properly, and that it will become more possible to use more than
;; one instance of PG at a time.  The disadvantage is that it is more
;; complicated, and less "object-oriented" than the previous approach.
;;
;; There are two mechanisms for accessing generic vars:
;;
;; (proof-ass name)  or (proof-assistant-name)
;;
;;

(require 'proof-site)			; proof-assitant-symbol
(require 'proof-compat)			; pg-custom-undeclare-variable
(require 'proof-autoloads)		; proof-debug

;;; Code:

(defmacro deflocal (var value &optional docstring)
  "Define a buffer local variable VAR with default value VALUE."
 `(progn
    (defvar ,var nil ,docstring)
    (make-variable-buffer-local (quote ,var))
    (setq-default ,var ,value)))

(deflocal proof-buffer-type nil
  "Symbol for the type of this buffer: 'script, 'shell, 'goals, or 'response.")


;;
;; Main macros
;;

(defmacro proof-ass-sym (sym)
  "Return the symbol for SYM for the current prover.  SYM not evaluated.
This macro should only be called once a specific prover is known."
  `(intern (concat (symbol-name proof-assistant-symbol) "-"
		   (symbol-name ',sym))))

(defmacro proof-ass-symv (sym)
  "Return the symbol for SYM for the current prover.  SYM evaluated.
This macro should only be invoked once a specific prover is engaged."
  `(intern (concat (symbol-name proof-assistant-symbol) "-"
		   (symbol-name ,sym))))

(defmacro proof-ass (sym)
  "Return the value for SYM for the current prover.
This macro should only be invoked once a specific prover is engaged."
  `(symbol-value (intern (concat (symbol-name proof-assistant-symbol) "-"
				 (symbol-name ',sym)))))

(defun proof-ass-differs-from-default (sym)
  "Return non-nil if SYM for current prover differs from its customize standard value."
  (let ((pasym (proof-ass-symv sym)))
    (not (equal (eval (car (get pasym 'standard-value)))
		(symbol-value pasym)))))

(defun proof-defpgcustom-fn (sym args)
  "Define a new customization variable <PA>-sym for current proof assistant.
Helper for macro `defpgcustom'."
  (let ((specific-var (proof-ass-symv sym))
	 (generic-var  (intern (concat "proof-assistant-" (symbol-name sym))))
	 (newargs     (if (member :group args) 
			  args 
			(append (list :group 
				      proof-assistant-internals-cusgrp)
				args))))
    (eval
     `(defcustom ,specific-var
	,@args))
    ;; For functions, we could simply use defalias.  Unfortunately there
    ;; is nothing similar for values, so we define a new set/get function.
    (eval
     `(defun ,generic-var (&optional newval)
	,(concat "Set or get value of " (symbol-name sym)
		 " for current proof assistant.
If NEWVAL is present, set the variable, otherwise return its current value.")
	(if newval
	    (setq ,specific-var newval)
	  ,specific-var)))))

(defun undefpgcustom (sym)
  (let ((specific-var (proof-ass-symv sym))
	(generic-var  (intern (concat "proof-assistant-" (symbol-name sym)))))
    (pg-custom-undeclare-variable specific-var)
    (fmakunbound generic-var)))

(defmacro defpgcustom (sym &rest args)
  "Define a new customization variable <PA>-SYM for the current proof assistant.
This is intended for defining settings which are useful for any prover,
but which the user may require different values of across provers.

The function proof-assistant-<SYM> is also defined, which can be used in the
generic portion of Proof General to access the value for the current prover.

Arguments are as for `defcustom', which see.  If a :group argument is
not supplied, the setting will be added to the internal settings for the
current prover (named <PA>-config)."
  `(proof-defpgcustom-fn (quote ,sym) (quote ,args)))

(defun proof-defpgdefault-fn (sym value)
  "Helper for `defpgdefault', which see.  SYM and VALUE are evaluated."
  ;; NB: we need this because nothing in customize library seems to do
  ;; the right thing.
  (let ((symbol  (proof-ass-symv sym)))
    (set-default symbol
		 (cond
		  ;; Use saved value if it's set
		  ((get symbol 'saved-value)
		   (car (get symbol 'saved-value)))
		  ;; Otherwise override old default with new one
		  (t
		   value)))))

(defmacro defpgdefault (sym value)
  "Set default for the proof assistant specific variable <PA>-SYM to VALUE.
This should be used in prover-specific code to alter the default values
for prover specific settings.

Usage: (defpgdefault SYM VALUE)"
    `(proof-defpgdefault-fn (quote ,sym) ,value))

;;
;; Make a function named for the current proof assistant.
;;
(defmacro defpgfun (name arglist &rest args)
  "Define function <PA>-SYM as for defun."
  `(defun ,(proof-ass-symv name) ,arglist
     ,@args))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Prover-assistant specific customizations
;; which are recorded in `proof-assistant-settings'
;;

;;; autoload for compiled version: used in macro proof-defpacustom
;;;###autoload
(defun proof-defpacustom-fn (name val args)
  "As for macro `defpacustom' but evaluating arguments."
  (let (newargs setting evalform type descr)
    (while args
      (cond
       ((eq (car args) :setting)
	(setq setting (cadr args))
	(setq args (cdr args)))
       ((eq (car args) :eval)
	(setq evalform (cadr args))
	(setq args (cdr args)))
       ((eq (car args) :pgipcmd)
	;; Construct a function which yields a PGIP string
	(setq setting `(lambda (x)
			  (pg-pgip-string-of-command (proof-assistant-format ,(cadr args) x))))
	(setq args (cdr args)))
       ((eq (car args) :pggroup)
	;; use the group as a prefix to the name, and set a pggroup property on it
	(setq name (intern (concat (downcase (cadr args)) ":" (symbol-name name))))
	(put name 'pggroup (cadr args))
	(setq args (cdr args)))
       ((eq (car args) :pgdynamic) 
	(put name 'pgdynamic (cadr args))
	(setq args (cdr args)))
       ((eq (car args) :type)
	(setq type (cadr args))
	(if (eq (eval type) 'float)
	    (setq type (quote 'number))) ; widget type for defcustom
	(setq args (cdr args))
	(setq newargs (cons type (cons :type newargs))))
       (t ; first element, description
	(setq newargs (cons (car args) newargs))))
      (setq args (cdr args)))
    (setq newargs (reverse newargs))
    (setq descr (car-safe newargs))
    (unless (and type
		  (or (eq (eval type) 'boolean)
		      (eq (eval type) 'integer)
		      (eq (eval type) 'number)
		      (eq (eval type) 'string)))
      (error "defpacustom: missing :type keyword or wrong :type value"))

    ;; Error in case a defpacustom is repeated.
    (when (assq name proof-assistant-settings)
      (error "defpacustom: Proof assistant setting %s re-defined!"
	     name))

    (eval
     `(defpgcustom ,name ,val
	,@newargs
	:set 'proof-set-value
	:group (quote ,proof-assistant-cusgrp)))
    (cond
     (evalform
      (eval
       `(defpgfun ,name ()
	  ,evalform)))
     (setting
      (eval
       `(defpgfun ,name ()
	  (proof-assistant-invisible-command-ifposs
	   (proof-assistant-settings-cmd (quote ,name)))))))
    (setq proof-assistant-settings
	  (cons (list name setting (eval type) descr)
		proof-assistant-settings))))

;;;###autoload
(defmacro defpacustom (name val &rest args)
  "Define a setting NAME for the current proof assistant, default VAL.
Mainly intended for configuring settings of running provers,
which can be changed by sending commands.

In this case, NAME stands for the internal setting, flag, etc,
for the proof assistant, and a :setting and :type value should be
provided.  The :type of NAME should be one of 'integer, 'float,
'boolean, 'string.

The function `proof-assistant-format' is used to format VAL.

This macro invokes the standard Emacs `defcustom' macro, so this
also defines a customizable setting inside Emacs.  The
customization variable is automatically put into the group
named after the prover.

If NAME corresponds instead to a PG internal setting, then a form :eval to
evaluate can be provided instead.

Additional properties in the ARGS prop list may include:

 pggroup   string    A grouping name for the setting, in case there are many.
		     For example, \"Timing\", \"Tracing\", etc.  Used
		     to generate sub-menus in the UI.

 pgipgcmd  string    Alternative to :setting.
		     Send a PGIP formatted command based on given string.

 pgdynamic flag      If flag is non-nil, this setting is a dynamic one
		     that is particular to the running instance of the prover.
		     Automatically set by preferences configured from PGIP 
		     askprefs message.

This macro also extends the `proof-assistant-settings' list."
  (eval-when-compile
    (if (boundp 'proof-assistant-symbol)
	;; declare variable to compiler to prevent warnings
	(eval `(defvar ,(proof-ass-sym name) nil "Dummy for compilation."))))
  `(proof-defpacustom-fn (quote ,name) (quote ,val) (quote ,args)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Evaluation once proof assistant is known
;;

(defmacro proof-eval-when-ready-for-assistant (&rest body)
  "Evaluate BODY once the proof assistant is determined (possibly now)."
  `(if (and (boundp 'proof-assistant-symbol) proof-assistant-symbol)
       (progn ,@body)
     (add-hook 'proof-ready-for-assistant-hook (lambda () ,@body))))



(provide 'pg-pamacs)
;;; pg-pamacs.el ends here
