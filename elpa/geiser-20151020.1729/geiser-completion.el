;;; geiser-completion.el -- tab completion

;; Copyright (C) 2009, 2010, 2011, 2012 Jose Antonio Ortega Ruiz

;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the Modified BSD License. You should
;; have received a copy of the license along with this program. If
;; not, see <http://www.xfree86.org/3.3.6/COPYRIGHT2.html#5>.

;; Start date: Mon Feb 09, 2009 22:21



(require 'geiser-impl)
(require 'geiser-eval)
(require 'geiser-log)
(require 'geiser-syntax)
(require 'geiser-base)

(require 'comint)
(require 'minibuffer)


;;; Minibuffer maps:

(defvar geiser-completion--minibuffer-map
  (let ((map (make-keymap)))
    (set-keymap-parent map minibuffer-local-completion-map)
    (define-key map "?" 'self-insert-command)
    map))

(defvar geiser-completion--module-minibuffer-map
  (let ((map (make-keymap)))
    (set-keymap-parent map minibuffer-local-completion-map)
    (define-key map " " 'self-insert-command)
    (define-key map "?" 'self-insert-command)
    map))


;;; Completion functionality:

(defvar geiser-completion--binding-forms nil)
(geiser-impl--register-local-variable
 'geiser-completion--binding-forms 'binding-forms nil
 "A list of forms introducing local bindings, a la let or lambda.")

(defvar geiser-completion--binding-forms* nil)
(geiser-impl--register-local-variable
 'geiser-completion--binding-forms* 'binding-forms* nil
 "A list of forms introducing nested local bindings, a la let*.")

(defsubst geiser-completion--locals ()
  (geiser-syntax--locals-around-point geiser-completion--binding-forms
                                      geiser-completion--binding-forms*))

(defun geiser-completion--symbol-list (prefix)
  (geiser--del-dups
   (append (all-completions prefix (geiser-completion--locals))
           (geiser-eval--send/result `(:eval (:ge completions ,prefix))))))

(defsubst geiser-completion--module-list (prefix)
  (geiser-eval--send/result `(:eval (:ge module-completions ,prefix))))

(defvar geiser-completion--symbol-list-func
  (completion-table-dynamic 'geiser-completion--symbol-list))

(defvar geiser-completion--module-list-func
  (completion-table-dynamic 'geiser-completion--module-list))

(defun geiser-completion--complete (prefix modules)
  (if modules (geiser-completion--module-list prefix)
    (geiser-completion--symbol-list prefix)))

(defvar geiser-completion--symbol-history nil)

(defun geiser-completion--read-symbol (prompt &optional default history)
  (let ((minibuffer-local-completion-map geiser-completion--minibuffer-map))
    (make-symbol (completing-read prompt
                                  geiser-completion--symbol-list-func
                                  nil nil nil
                                  (or history
                                      geiser-completion--symbol-history)
                                  (or default (geiser--symbol-at-point))))))

(defvar geiser-completion--module-history nil)

(defun geiser-completion--read-module (&optional prompt default history)
  (let ((minibuffer-local-completion-map
         geiser-completion--module-minibuffer-map))
    (completing-read (or prompt "Module name: ")
                     geiser-completion--module-list-func
                     nil nil nil
                     (or history geiser-completion--module-history)
                     default)))

(defvar geiser-completion--symbol-begin-function nil)

(defun geiser-completion--def-symbol-begin (module)
  (save-excursion (skip-syntax-backward "^-()>") (point)))

(geiser-impl--register-local-method
 'geiser-completion--symbol-begin-function 'find-symbol-begin
 'geiser-completion--def-symbol-begin
 "An optional function finding the position of the beginning of
the identifier around point. Takes a boolean, indicating whether
we're looking for a module name.")

(defun geiser-completion--symbol-begin (module)
  (funcall geiser-completion--symbol-begin-function module))

(defun geiser-completion--module-at-point ()
  (save-excursion
    (goto-char (geiser-completion--symbol-begin t))
    (ignore-errors (thing-at-point 'sexp))))

(defsubst geiser-completion--prefix (module)
  (buffer-substring-no-properties (geiser-completion--symbol-begin module)
                                  (point)))

(defsubst geiser-completion--prefix-end (beg mod)
  (unless (or (eq beg (point-max))
              (member (char-syntax (char-after beg))
                      (if mod '(?\" ?\)) '(?\" ?\( ?\)))))
    (let ((pos (point)))
      (condition-case nil
          (save-excursion
            (goto-char beg)
            (forward-sexp 1)
            (when (>= (point) pos)
              (point)))
        (scan-error pos)))))

(defun geiser-completion--thing-at-point (module &optional predicate)
  (with-syntax-table scheme-mode-syntax-table
    (let* ((beg (geiser-completion--symbol-begin module))
           (end (or (geiser-completion--prefix-end beg module) beg))
           (prefix (and (> end beg) (buffer-substring-no-properties beg end)))
           (prefix (and prefix
                        (if (string-match "\\([^-]+\\)-" prefix)
                            (match-string 1 prefix)
                          prefix)))
           (cmps (and prefix (geiser-completion--complete prefix module))))
      (and cmps (list beg end cmps)))))

(defun geiser-completion--for-symbol (&optional predicate)
  (geiser-completion--thing-at-point nil predicate))

(defun geiser-completion--for-module (&optional predicate)
  (geiser-completion--thing-at-point t predicate))

(defun geiser-completion--for-filename ()
  (when (geiser-syntax--in-string-p)
    (let ((comint-completion-addsuffix "\""))
      (comint-dynamic-complete-filename))))

(defun geiser-completion--setup (enable)
  (set (make-local-variable 'completion-at-point-functions)
       (if enable
           '(geiser-completion--for-symbol
             geiser-completion--for-module
             geiser-completion--for-filename)
         (default-value 'completion-at-point-functions))))

(defun geiser-completion--complete-module ()
  "Complete module name at point."
  (interactive)
  (let ((completion-at-point-functions '(geiser-completion--for-module)))
    (call-interactively 'completion-at-point)))


;;; Smart tab mode:

(make-variable-buffer-local
 (defvar geiser-smart-tab-mode-string " SmartTab"
   "Modeline indicator for geiser-smart-tab-mode"))

(define-minor-mode geiser-smart-tab-mode
  "Toggle smart tab mode.
With no argument, this command toggles the mode.
Non-null prefix argument turns on the mode.
Null prefix argument turns off the mode.

When this mode is enable, TAB will indent if at point is at
beginning of line or after a white space or closing parenthesis,
and will try completing symbol at point otherwise."
  :init-value nil
  :lighter geiser-smart-tab-mode-string
  :group 'geiser-mode
  (set (make-local-variable 'tab-always-indent)
       (if geiser-smart-tab-mode
           'complete
         (default-value 'tab-always-indent))))


(provide 'geiser-completion)
