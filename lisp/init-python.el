;; -*- coding: utf-8; lexical-binding: t; -*-

(setq interpreter-mode-alist
      (cons '("python" . python-mode) interpreter-mode-alist))

(eval-after-load 'python
  '(progn
     ;; run command `pip install jedi flake8 importmagic` in shell,
     ;; or just check https://github.com/jorgenschaefer/elpy
     (unless (or (is-buffer-file-temp)
                 (not buffer-file-name)
                 ;; embed python code in org file
                 (string= (file-name-extension buffer-file-name) "org"))

       (elpy-enable)

       ;; Use IPython for REPL
       (setq python-shell-interpreter "ipython"
             python-shell-interpreter-args "--simple-prompt -i"
             python-shell-prompt-detect-failure-warning nil)
       (add-to-list 'python-shell-completion-native-disabled-interpreters
                    "jupyter")
       
       ;; Enable Flycheck
       (when (require 'flycheck nil t)
         (setq elpy-modules (delq 'elpy-module-flymake elpy-modules))
         (add-hook 'elpy-mode-hook 'flycheck-mode))

       ;; Enable autopep8
       (require 'py-autopep8)
       (add-hook 'elpy-mode-hook 'py-autopep8-enable-on-save)
       )

     ;; http://emacs.stackexchange.com/questions/3322/python-auto-indent-problem/3338#3338
     ;; emacs 24.4 only
     (setq electric-indent-chars (delq ?: electric-indent-chars))))

(provide 'init-python)
