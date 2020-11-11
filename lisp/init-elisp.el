;; -*- coding: utf-8; lexical-binding: t; -*-
(defun elisp-mode-hook-setup ()
  (unless (is-buffer-file-temp)
    (my-ensure 'eldoc)
    (turn-on-eldoc-mode)
    (enable-paredit-mode)
    (rainbow-delimiters-mode t)

    ;; Locally set `hippie-expand' completion functions for use with Emacs Lisp.
    (make-local-variable 'hippie-expand-try-functions-list)
    (push 'try-complete-lisp-symbol hippie-expand-try-functions-list)
    (push 'try-complete-lisp-symbol-partially hippie-expand-try-functions-list)

    (checkdoc-minor-mode 1)))
(add-hook 'emacs-lisp-mode-hook 'elisp-mode-hook-setup)

(provide 'init-elisp)
