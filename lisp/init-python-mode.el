(autoload 'doctest-mode "doctest-mode" "Python doctest editing mode." t)

(setq interpreter-mode-alist
      (cons '("python" . python-mode) interpreter-mode-alist))

(eval-after-load 'python
  '(require 'flymake-python-pyflakes))

(add-hook 'python-mode-hook
          '(lambda ()
             (unless (is-buffer-file-temp)
               (anaconda-mode)
               (add-to-list 'company-backends 'company-anaconda)
               (eldoc-mode)
               (if (executable-find "pyflakes")
                   (flymake-python-pyflakes-load))
               ;; http://emacs.stackexchange.com/questions/3322/python-auto-indent-problem/3338#3338
               ;; emacs 24.4 only
               (setq electric-indent-chars (delq ?: electric-indent-chars))
               )))

(provide 'init-python-mode)
