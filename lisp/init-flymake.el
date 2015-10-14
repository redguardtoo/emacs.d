;; we use improved version of flymake
;; https://github.com/illusori/emacs-flymake

;; I want to see at most the first 4 errors for a line
(setq flymake-number-of-errors-to-display 4)

;; Let's run 2 checks at once instead.
(setq flymake-max-parallel-syntax-checks 2)

(setq flymake-gui-warnings-enabled nil)

;; Stop flymake from breaking when ruby-mode is invoked by mmm-mode,
;; at which point buffer-file-name is nil
(eval-after-load 'flymake
  '(progn
     (defun flymake-can-syntax-check-file (file-name)
       "Determine whether we can syntax check FILE-NAME.
Return nil if we cannot, non-nil if we can."
       (if (and file-name (flymake-get-init-function file-name)) t nil))
     ))

(provide 'init-flymake)
