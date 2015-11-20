;; geiser-impl.el -- generic support for scheme implementations

;; Copyright (C) 2009, 2010, 2012, 2013, 2015 Jose Antonio Ortega Ruiz

;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the Modified BSD License. You should
;; have received a copy of the license along with this program. If
;; not, see <http://www.xfree86.org/3.3.6/COPYRIGHT2.html#5>.

;; Start date: Sat Mar 07, 2009 23:32



(require 'geiser-custom)
(require 'geiser-base)

(require 'help-fns)


;;; Customization:

(defgroup geiser-implementation nil
  "Generic support for multiple Scheme implementations."
  :group 'geiser)

(geiser-custom--defcustom geiser-default-implementation nil
  "Symbol naming the default Scheme implementation."
  :type 'symbol
  :group 'geiser-implementation)

(geiser-custom--defcustom geiser-active-implementations '(guile racket chicken)
  "List of active installed Scheme implementations."
  :type '(repeat symbol)
  :group 'geiser-implementation)

(geiser-custom--defcustom geiser-implementations-alist nil
  "A map from regular expressions or directories to implementations.
When opening a new file, its full path will be matched against
each one of the regular expressions or directories in this map in order to
determine its scheme flavour."
  :type '(repeat (list (choice (group :tag "Regular expression"
                                      (const regexp) regexp)
                               (group :tag "Directory"
                                      (const dir) directory))
                       symbol))
  :group 'geiser-implementation)


;;; Implementation registry:

(defvar geiser-impl--registry nil)
(defvar geiser-impl--load-files nil)
(defvar geiser-impl--method-docs nil)
(defvar geiser-impl--local-methods nil)
(defvar geiser-impl--local-variables nil)

(geiser-custom--memoize 'geiser-impl--load-files)

(make-variable-buffer-local
 (defvar geiser-impl--implementation nil))

(defsubst geiser-impl--impl-str (&optional impl)
  (let ((impl (or impl geiser-impl--implementation)))
    (and impl (capitalize (format "%s" impl)))))

(defsubst geiser-impl--feature (impl)
  (intern (format "geiser-%s" impl)))

(defsubst geiser-impl--load-impl (impl)
  (require (geiser-impl--feature impl)
           (cdr (assq impl geiser-impl--load-files))
           t))

(defsubst geiser-impl--methods (impl)
  (cdr (assq impl geiser-impl--registry)))

(defun geiser-impl--method (method &optional impl)
  (let ((impl (or impl
                  geiser-impl--implementation
                  geiser-default-implementation)))
    (cadr (assq method (geiser-impl--methods impl)))))

(defun geiser-impl--call-method (method impl &rest args)
  (let ((fun (geiser-impl--method method impl)))
    (when (functionp fun) (apply fun args))))

(defun geiser-impl--method-doc (method doc user)
  (let* ((user (if user (format " Used via `%s'." user) ""))
         (extra-doc (format "%s%s" doc user)))
    (add-to-list 'geiser-impl--method-docs (cons method extra-doc))
    (setq geiser-impl--method-docs
          (sort geiser-impl--method-docs
                (lambda (a b) (string< (symbol-name (car a))
                                  (symbol-name (car b))))))
    (put method 'function-documentation doc)))

(defun geiser-implementation-help ()
  "Shows a buffer with help on defining new supported Schemes."
  (interactive)
  (help-setup-xref (list #'geiser-implementation-help) t)
  (save-excursion
    (with-help-window (help-buffer)
      (princ "Geiser: supporting new Scheme implementations.\n\n")
      (princ "Use `define-geiser-implementation' to define ")
      (princ "new implementations")
      (princ "\n\n  (define-geiser-implementation NAME &rest METHODS)\n\n")
      (princ (documentation 'define-geiser-implementation))
      (princ "\n\nMethods used to define an implementation:\n\n")
      (dolist (m geiser-impl--method-docs)
        (let ((p (with-current-buffer (help-buffer) (point))))
          (princ (format "%s: " (car m)))
          (princ (cdr m))
          (with-current-buffer (help-buffer)
            (fill-region-as-paragraph p (point)))
          (princ "\n\n")))
      (with-current-buffer standard-output (buffer-string)))))

(defun geiser-impl--register-local-method (var-name method fallback doc)
  (add-to-list 'geiser-impl--local-methods (list var-name method fallback))
  (geiser-impl--method-doc method doc var-name)
  (put var-name 'function-documentation doc))

(defun geiser-impl--register-local-variable (var-name method fallback doc)
  (add-to-list 'geiser-impl--local-variables (list var-name method fallback))
  (geiser-impl--method-doc method doc var-name)
  (put var-name 'variable-documentation doc))

(defmacro geiser-impl--define-caller (fun-name method arglist doc)
  (let ((impl (make-symbol "implementation-name")))
    `(progn
       (defun ,fun-name ,(cons impl arglist) ,doc
         (geiser-impl--call-method ',method ,impl ,@arglist))
       (geiser-impl--method-doc ',method ,doc ',fun-name))))
(put 'geiser-impl--define-caller 'lisp-indent-function 3)

(defun geiser-impl--register (file impl methods)
  (let ((current (assq impl geiser-impl--registry)))
    (if current (setcdr current methods)
      (push (cons impl methods) geiser-impl--registry))
    (push (cons impl file) geiser-impl--load-files)))

(defsubst geiser-activate-implementation (impl)
  (add-to-list 'geiser-active-implementations impl))

(defsubst geiser-deactivate-implementation (impl)
  (setq geiser-active-implementations
        (delq impl geiser-active-implementations)))

(defsubst geiser-impl--active-p (impl)
  (memq impl geiser-active-implementations))


;;; Defining implementations:

(defun geiser-impl--normalize-method (m)
  (when (and (listp m)
             (= 2 (length m))
             (symbolp (car m)))
    (if (functionp (cadr m)) m
      `(,(car m) (lambda (&rest) ,(cadr m))))))

(defun geiser-impl--define (file name parent methods)
  (let* ((methods (mapcar 'geiser-impl--normalize-method methods))
         (methods (delq nil methods))
         (inherited-methods (and parent (geiser-impl--methods parent)))
         (methods (append methods
                          (dolist (m methods inherited-methods)
                            (setq inherited-methods
                                  (assq-delete-all m inherited-methods))))))
    (geiser-impl--register file name methods)))

(defmacro define-geiser-implementation (name &rest methods)
  "Defines a new supported Scheme implementation.
NAME can be either an unquoted symbol naming the implementation,
or a two-element list (NAME PARENT), with PARENT naming another
registered implementation from which to borrow methods not
defined in METHODS.

After NAME come the methods, each one a two element list of the
form (METHOD-NAME FUN-OR-VAR), where METHOD-NAME is one of the
needed methods (for a list, execute `geiser-implementation-help')
and a value, variable name or function name implementing it.
Omitted method names will return nil to their callers.

Here's how a typical call to this macro looks like:

  (define-geiser-implementation guile
    (binary geiser-guile--binary)
    (arglist geiser-guile--parameters)
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
    (display-help)
    (check-buffer geiser-guile--guess)
    (keywords geiser-guile--keywords)
    (case-sensitive geiser-guile-case-sensitive-p))

This macro also defines a runner function (run-NAME) and a
switcher (switch-to-NAME), and provides geiser-NAME."
  (let ((name (if (listp name) (car name) name))
        (parent (and (listp name) (cadr name))))
    (unless (symbolp name)
      (error "Malformed implementation name: %s" name))
    (let ((runner (intern (format "run-%s" name)))
          (switcher (intern (format "switch-to-%s" name)))
          (runner-doc (format "Start a new %s REPL." name))
          (switcher-doc (format "Switch to a running %s REPL, or start one."
                                name))
          (ask (make-symbol "ask")))
      `(progn
         (geiser-impl--define ,load-file-name ',name ',parent ',methods)
         (require 'geiser-repl)
         (require 'geiser-menu)
         (defun ,runner ()
           ,runner-doc
           (interactive)
           (run-geiser ',name))
         (defun ,switcher (&optional ,ask)
           ,switcher-doc
           (interactive "P")
           (switch-to-geiser ,ask ',name))
         (geiser-menu--add-impl ',name ',runner ',switcher)))))

(defun geiser-impl--add-to-alist (kind what impl &optional append)
  (add-to-list 'geiser-implementations-alist
               (list (list kind what) impl) append))


;;; Trying to guess the scheme implementation:

(make-variable-buffer-local
 (defvar geiser-scheme-implementation nil
   "Set this buffer local variable to specify the Scheme
implementation to be used by Geiser."))

(put 'geiser-scheme-implementation 'safe-local-variable 'symbolp)

(defun geiser-impl--match-impl (desc bn)
  (let ((rx (if (eq (car desc) 'regexp)
                (cadr desc)
              (format "^%s" (regexp-quote (cadr desc))))))
    (and rx (string-match-p rx bn))))

(defvar geiser-impl--impl-prompt-history nil)

(defun geiser-impl--read-impl (&optional prompt impls non-req)
  (let* ((impls (or impls geiser-active-implementations))
         (impls (mapcar 'symbol-name impls))
         (prompt (or prompt "Scheme implementation: ")))
    (intern (completing-read prompt impls nil (not non-req) nil
                             geiser-impl--impl-prompt-history
                             (and (car impls) (car impls))))))

(geiser-impl--define-caller geiser-impl--check-buffer check-buffer ()
  "Method called without arguments that should check whether the current
buffer contains Scheme code of the given implementation.")

(defun geiser-impl--guess (&optional prompt)
  (or geiser-impl--implementation
      (progn (hack-local-variables)
             (and (memq geiser-scheme-implementation
                        geiser-active-implementations)
                  geiser-scheme-implementation))
      (and (null (cdr geiser-active-implementations))
           (car geiser-active-implementations))
      (catch 'impl
        (dolist (impl geiser-active-implementations)
          (when (geiser-impl--check-buffer impl)
            (throw 'impl impl)))
        (let ((bn (buffer-file-name)))
          (when bn
            (dolist (x geiser-implementations-alist)
              (when (and (memq (cadr x) geiser-active-implementations)
                         (geiser-impl--match-impl (car x) bn))
                (throw 'impl (cadr x)))))))
      geiser-default-implementation
      (and prompt (geiser-impl--read-impl))))


;;; Using implementations:

(defsubst geiser-impl--registered-method (impl method fallback)
  (let ((m (geiser-impl--method method impl)))
    (if (fboundp m) m
      (or fallback (error "%s not defined for %s implementation"
                          method impl)))))

(defsubst geiser-impl--registered-value (impl method fallback)
  (let ((m (geiser-impl--method method impl)))
    (if (functionp m) (funcall m) fallback)))

(defun geiser-impl--set-buffer-implementation (&optional impl prompt)
  (let ((impl (or impl (geiser-impl--guess prompt))))
    (when impl
      (unless (geiser-impl--load-impl impl)
        (error "Cannot find %s implementation" impl))
      (setq geiser-impl--implementation impl)
      (dolist (m geiser-impl--local-methods)
        (set (make-local-variable (nth 0 m))
             (geiser-impl--registered-method impl (nth 1 m) (nth 2 m))))
      (dolist (m geiser-impl--local-variables)
        (set (make-local-variable (nth 0 m))
             (geiser-impl--registered-value impl (nth 1 m) (nth 2 m)))))))

(defmacro with--geiser-implementation (impl &rest body)
  (let* ((mbindings (mapcar (lambda (m)
                              `(,(nth 0 m)
                                (geiser-impl--registered-method ,impl
                                                                ',(nth 1 m)
                                                                ',(nth 2 m))))
                            geiser-impl--local-methods))
         (vbindings (mapcar (lambda (m)
                              `(,(nth 0 m)
                                (geiser-impl--registered-value ,impl
                                                               ',(nth 1 m)
                                                               ',(nth 2 m))))
                            geiser-impl--local-variables))
         (ibindings `((geiser-impl--implementation ,impl)))
         (bindings (append ibindings mbindings vbindings)))
    `(let* ,bindings ,@body)))
(put 'with--geiser-implementation 'lisp-indent-function 1)


;;; Reload support:

(defun geiser-impl-unload-function ()
  (dolist (imp (mapcar (lambda (i)
                         (geiser-impl--feature (car i)))
                       geiser-impl--registry))
    (when (featurep imp) (unload-feature imp t))))


(provide 'geiser-impl)
