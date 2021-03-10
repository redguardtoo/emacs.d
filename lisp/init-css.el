;; -*- coding: utf-8; lexical-binding: t; -*-

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
    (rainbow-mode 1)
    (counsel-css-imenu-setup)
    (setq imenu-create-index-function 'counsel-css--imenu-create-index-function)))
(add-hook 'css-mode-hook 'css-mode-hook-setup)

;; `css-mode' has better imenu support and won't force flymake to create rubbish files.
;; besides, scss/sass is outdated. We use postcss or css in js these days.
(my-add-auto-mode 'css-mode "\\.scss$")

(provide 'init-css)