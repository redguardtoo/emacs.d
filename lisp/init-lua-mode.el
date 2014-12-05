(defun my-lua-mode-setup ()
  (setq safe-local-variable-values
        '((lua-indent-level . 2)
          (lua-indent-level . 3)
          (lua-indent-level . 4)
          (lua-indent-level . 8)))
  (flymake-lua-load))

(add-hook 'lua-mode-hook 'my-lua-mode-setup)
(provide 'init-lua-mode)
