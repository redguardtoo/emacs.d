;; geiser-company.el -- integration with company-mode

;; Copyright (C) 2009, 2010, 2011, 2012, 2013, 2014 Jose Antonio Ortega Ruiz

;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the Modified BSD License. You should
;; have received a copy of the license along with this program. If
;; not, see <http://www.xfree86.org/3.3.6/COPYRIGHT2.html#5>.

;; Start date: Mon Aug 24, 2009 12:44



(require 'geiser-autodoc)
(require 'geiser-completion)
(require 'geiser-edit)
(require 'geiser-base)
(require 'geiser-doc)

(eval-when-compile (require 'cl))


;;; Helpers:

(make-variable-buffer-local
 (defvar geiser-company--enabled-flag nil))

(make-variable-buffer-local
 (defvar geiser-company--autodoc-flag nil))

(make-variable-buffer-local
 (defvar geiser-company--completions nil))

(defun geiser-company--candidates (prefix)
  (and (equal prefix (car geiser-company--completions))
       (cdr geiser-company--completions)))

(defun geiser-company--doc (id)
  (ignore-errors
    (when (not (geiser-autodoc--inhibit))
      (let ((help (geiser-autodoc--autodoc `((,id 0)))))
        (and help (substring-no-properties help))))))

(defun geiser-company--doc-buffer (id)
  (let* ((impl geiser-impl--implementation)
         (module (geiser-doc-module (geiser-eval--get-module) impl))
         (symbol (make-symbol id))
         (ds (geiser-doc--get-docstring symbol module)))
    (if (or (not ds) (not (listp ds)))
        (message "No documentation available for '%s'" symbol)
      (with-current-buffer (get-buffer-create "*company-documentation*")
        (geiser-doc--render-docstring ds symbol module impl)
        (current-buffer)))))

(defun geiser-company--location (id)
  (ignore-errors
    (when (not (geiser-autodoc--inhibit))
      (let ((id (make-symbol id)))
        (condition-case nil
            (geiser-edit-module id 'noselect)
          (error (geiser-edit-symbol id 'noselect)))))))

(defun geiser-company--prefix-at-point ()
  (when (and (not (geiser-autodoc--inhibit)) geiser-company--enabled-flag)
    (if (nth 8 (syntax-ppss)) 'stop
      (let* ((prefix (and (looking-at-p "\\_>")
                          (geiser-completion--prefix nil)))
             (cmps1 (and prefix
                         (geiser-completion--complete prefix nil)))
             (cmps2 (and prefix
                         (geiser-completion--complete prefix t)))
             (mprefix (and (not cmps1) (not cmps2)
                           (geiser-completion--prefix t)))
             (cmps3 (and mprefix (geiser-completion--complete mprefix t)))
             (cmps (or cmps3 (append cmps1 cmps2)))
             (prefix (or mprefix prefix)))
        (setq geiser-company--completions (cons prefix cmps))
        prefix))))


;;; Activation

(defun geiser-company--setup (enable)
  (setq geiser-company--enabled-flag enable)
  (when (fboundp 'geiser-company--setup-company)
    (geiser-company--setup-company enable)))

(defun geiser-company--inhibit-autodoc (ignored)
  (when (setq geiser-company--autodoc-flag geiser-autodoc-mode)
    (geiser-autodoc-mode -1)))

(defun geiser-company--restore-autodoc (&optional ignored)
  (when geiser-company--autodoc-flag
    (geiser-autodoc-mode 1)))


;;; Company activation

(eval-after-load "company"
  '(progn
     (defun geiser-company-backend (command &optional arg &rest ignored)
       "A `company-mode' completion back-end for `geiser-mode'."
       (interactive (list 'interactive))
       (case command
         ('interactive (company-begin-backend 'geiser-company-backend))
         ('prefix (geiser-company--prefix-at-point))
         ('candidates (geiser-company--candidates arg))
         ('meta (geiser-company--doc arg))
         ('doc-buffer (geiser-company--doc-buffer arg))
         ('location (geiser-company--location arg))
         ('sorted t)))
     (defun geiser-company--setup-company (enable)
       (set (make-local-variable 'company-default-lighter) "/C")
       (set (make-local-variable 'company-echo-delay) 0.01)
       (set (make-local-variable 'company-backends)
            (and enable '(geiser-company-backend)))
       (company-mode (if enable 1 -1)))
     (add-hook 'company-completion-finished-hook
               'geiser-company--restore-autodoc)
     (add-hook 'company-completion-cancelled-hook
               'geiser-company--restore-autodoc)
     (add-hook 'company-completion-started-hook
               'geiser-company--inhibit-autodoc)
     (define-key company-active-map (kbd "M-`")
       (lambda ()
         (interactive)
         (company-cancel)
         (call-interactively 'geiser-completion--complete-module)))))



(provide 'geiser-company)
