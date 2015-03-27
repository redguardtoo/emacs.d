;; ----------------------------------------------------------------------------
;; Paredit
;; ----------------------------------------------------------------------------
(autoload 'enable-paredit-mode "paredit")

(setq-default initial-scratch-message
              (concat ";; Happy hacking " (or user-login-name "") " - Emacs loves you!\n\n"))

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


;; Use paredit in the minibuffer
(add-hook 'minibuffer-setup-hook 'conditionally-enable-paredit-mode)

(defvar paredit-minibuffer-commands '(eval-expression
                                      pp-eval-expression
                                      eval-expression-with-eldoc
                                      ibuffer-do-eval
                                      ibuffer-do-view-and-eval)
  "Interactive commands for which paredit should be enabled in the minibuffer.")

(defun conditionally-enable-paredit-mode ()
  "Enable paredit during lisp-related minibuffer commands."
  (if (memq this-command paredit-minibuffer-commands)
      (enable-paredit-mode)))





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
