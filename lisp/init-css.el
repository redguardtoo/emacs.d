;; Colourise CSS colour literals
;; web-mode does not like rainbow-mode
(dolist (hook '(css-mode-hook))
  (add-hook hook 'rainbow-mode))

(defun my-css-imenu-make-index ()
  (save-excursion
    (imenu--generic-function '((nil "^ *\\([a-zA-Z0-9&,.: _-]+\\) *{ *$" 1)
                               ("Variable" "^ *\\$\\([a-zA-Z0-9_]+\\) *:" 1)
                               ;; post-css mixin
                               ("Function" "^ *@define-mixin +\\([^ ]+\\)" 1)))))

;; node plugins can compile css into javascript
;; flymake-css is obsolete
(defun css-mode-hook-setup ()
  (unless (is-buffer-file-temp)
    (setq imenu-create-index-function 'my-css-imenu-make-index)))
(add-hook 'css-mode-hook 'css-mode-hook-setup)

;; compile *.scss to *.css on the pot could break the project build
(setq scss-compile-at-save nil)
(defun scss-mode-hook-setup ()
  (unless (is-buffer-file-temp)
    (setq imenu-create-index-function 'my-css-imenu-make-index)))
(add-hook 'scss-mode-hook 'scss-mode-hook-setup)

(provide 'init-css)