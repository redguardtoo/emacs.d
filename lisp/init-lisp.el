;; -*- coding: utf-8; lexical-binding: t; -*-

(defun show-scratch-buffer-message ()
  (let* ((fortune-prog (or (executable-find "fortune-zh")
                           (executable-find "fortune"))))
    (cond
     (fortune-prog
      (format
       ";; %s\n\n"
       (replace-regexp-in-string
        "\n" "\n;; " ; comment each line
        (replace-regexp-in-string
         "\\(\n$\\|\\|\\[m *\\|\\[[0-9][0-9]m *\\)" ""    ; remove trailing linebreak
         (shell-command-to-string fortune-prog)))))
     (t
      (concat ";; Happy hacking "
              (or user-login-name "")
              " - Emacs loves you!\n\n")))))

(setq-default initial-scratch-message (show-scratch-buffer-message))

;; racket
(add-to-list 'auto-mode-alist '("\\.rkt\\'" . lisp-mode))

;; A quick way to jump to the definition of a function given its key binding
(global-set-key (kbd "C-h K") 'find-function-on-key)

(eval-after-load 'paredit
  '(progn
     (diminish 'paredit-mode " Par")))


(defvar paredit-minibuffer-commands '(eval-expression
                                      pp-eval-expression
                                      eval-expression-with-eldoc
                                      ibuffer-do-eval
                                      ibuffer-do-view-and-eval)
  "Interactive commands for which paredit should be enabled in the minibuffer.")

(defun my-swap-sexps (&optional num)
  "Swap two lisp sexps."
  (interactive "P")
  (let* ((c (following-char)))
    (cond
     (num
      (unless (eq c 40)
        (goto-char (line-beginning-position))))
     (t
      (unless (eq c 40)
        (goto-char (line-end-position))
        (goto-char (+ (point) 1)))))
    (transpose-sexps 1)
    (backward-sexp)))

;; ----------------------------------------------------------------------------
;; Enable desired features for all lisp modes
;; ----------------------------------------------------------------------------
(defun sanityinc/lisp-setup ()
  "Enable features useful in any Lisp mode."
  (enable-paredit-mode)
  (rainbow-delimiters-mode t)
  (turn-on-eldoc-mode))

(let* ((hooks '(lisp-mode-hook
                inferior-lisp-mode-hook
                lisp-interaction-mode-hook)))
  (dolist (hook hooks)
    (add-hook hook 'sanityinc/lisp-setup)))

(provide 'init-lisp)
