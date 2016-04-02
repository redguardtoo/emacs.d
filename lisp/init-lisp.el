;; Paredit
;; ----------------------------------------------------------------------------
(setq-default initial-scratch-message
              (if (executable-find "fortune")
                  (format
                   ";; %s\n\n"
                   (replace-regexp-in-string
                    "\n" "\n;; " ; comment each line
                    (replace-regexp-in-string
                     "\n$" ""    ; remove trailing linebreak
                     (shell-command-to-string "fortune"))))
                (concat ";; Happy hacking "
                        (or user-login-name "")
                        " - Emacs loves you!\n\n")))

;; racket
(add-to-list 'auto-mode-alist '("\\.rkt\\'" . lisp-mode))

;; {{ scheme setup
(setq scheme-program-name "guile")
(eval-after-load 'scheme-mode
  '(progn
     (require 'quack)))
;; }}

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

(defun conditionally-paredit-mode (flag)
  "Enable paredit during lisp-related minibuffer commands."
  (if (memq this-command paredit-minibuffer-commands)
      (paredit-mode flag)))






;; ----------------------------------------------------------------------------
;; Highlight current sexp
;; ----------------------------------------------------------------------------
;; Prevent flickery behaviour due to hl-sexp-mode unhighlighting before each command
(eval-after-load 'hl-sexp
  '(defadvice hl-sexp-mode (after unflicker (turn-on) activate)
     (when turn-on
       (remove-hook 'pre-command-hook #'hl-sexp-unhighlight))))

;; ----------------------------------------------------------------------------
;; Enable desired features for all lisp modes
;; ----------------------------------------------------------------------------
(defun sanityinc/lisp-setup ()
  "Enable features useful in any Lisp mode."
  (enable-paredit-mode)
  (rainbow-delimiters-mode t)
  (turn-on-eldoc-mode))

(let* ((lispy-hooks '(lisp-mode-hook
                      inferior-lisp-mode-hook
                      lisp-interaction-mode-hook)))
  (dolist (hook lispy-hooks)
    (add-hook hook 'sanityinc/lisp-setup)))

(provide 'init-lisp)
