;; Colourise CSS colour literals
;; web-mode does not like rainbow-mode
(autoload 'rainbow-mode "rainbow-mode" nil t)
(dolist (hook '(css-mode-hook))
  (add-hook hook 'rainbow-mode))

(defun maybe-flymake-css-load ()
  "Activate flymake-css as necessary, but not in derived modes."
  (when (eq major-mode 'css-mode)
    (flymake-css-load)))

(defun my-css-imenu-make-index ()
  (save-excursion
    (imenu--generic-function '((nil "^ *\\([^ ]+\\) *{ *$" 1)
                               ))))
(add-hook 'css-mode-hook
          (lambda ()
            (unless (is-buffer-file-temp)
              (setq imenu-create-index-function 'my-css-imenu-make-index)
              (maybe-flymake-css-load))))

(add-hook 'scss-mode-hook
          (lambda ()
            (unless (is-buffer-file-temp)
              (setq imenu-create-index-function 'my-css-imenu-make-index))))

(provide 'init-css)
