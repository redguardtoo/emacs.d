;; Colourise CSS colour literals
;; web-mode does not like rainbow-mode
(dolist (hook '(css-mode-hook))
  (add-hook hook 'rainbow-mode))

(defun maybe-flymake-css-load ()
  "Activate flymake-css as necessary, but not in derived modes."
  (if (and (eq major-mode 'css-mode)
           (not (buffer-too-big-p)))
    (flymake-css-load)))

(defun my-css-imenu-make-index ()
  (save-excursion
    (imenu--generic-function '((nil "^ *\\([^ ]+\\) *{ *$" 1)
                               ))))

(defun css-mode-hook-setup ()
  (unless (is-buffer-file-temp)
    (setq imenu-create-index-function 'my-css-imenu-make-index)
    (maybe-flymake-css-load)))
(add-hook 'css-mode-hook 'css-mode-hook-setup)

;; compile *.scss to *.css on the pot could break the project build
(setq scss-compile-at-save nil)
(defun scss-mode-hook-setup ()
  (unless (is-buffer-file-temp)
    (setq imenu-create-index-function 'my-css-imenu-make-index)))
(add-hook 'scss-mode-hook 'scss-mode-hook-setup)

(provide 'init-css)
