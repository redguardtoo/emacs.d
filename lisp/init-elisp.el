;; -*- coding: utf-8; lexical-binding: t; -*-

(defun set-up-hippie-expand-for-elisp ()
  "Locally set `hippie-expand' completion functions for use with Emacs Lisp."
  (make-local-variable 'hippie-expand-try-functions-list)
  (add-to-list 'hippie-expand-try-functions-list 'try-complete-lisp-symbol t)
  (add-to-list 'hippie-expand-try-functions-list 'try-complete-lisp-symbol-partially t))

(defun elisp-mode-hook-setup ()
  (unless (is-buffer-file-temp)
    (my-ensure 'eldoc)
    (turn-on-eldoc-mode)
    (enable-paredit-mode)
    (rainbow-delimiters-mode t)
    (set-up-hippie-expand-for-elisp)
    (checkdoc-minor-mode 1)))
(add-hook 'emacs-lisp-mode-hook 'elisp-mode-hook-setup)

(provide 'init-elisp)
