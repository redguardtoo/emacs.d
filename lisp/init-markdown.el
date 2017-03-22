(setq auto-mode-alist
      (cons '("\\.\\(md\\|markdown\\)\\'" . markdown-mode) auto-mode-alist))

(defun markdown-imenu-index ()
  (let* ((patterns '((nil "^#\\([# ]*[^#\n\r]+\\)" 1))))
    (save-excursion
      (imenu--generic-function patterns))))

(defun markdown-mode-hook-setup ()
  (setq imenu-create-index-function 'markdown-imenu-index))
(add-hook 'markdown-mode-hook 'markdown-mode-hook-setup)

(provide 'init-markdown)
