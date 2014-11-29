(require 'erlang-start)


(require 'flymake)
(setq flymake-log-level 3)

;; @see https://github.com/ten0s/syntaxerl
(defun flymake-compile-script-path (path)
  (let* ((temp-file (flymake-init-create-temp-buffer-copy
                     'flymake-create-temp-inplace))
         (local-file (file-relative-name
                      temp-file
                      (file-name-directory buffer-file-name))))
    (list path (list local-file))))

(defun flymake-syntaxerl ()
  (flymake-compile-script-path (file-truename "~/bin/syntaxerl")))

(add-hook 'erlang-mode-hook
          '(lambda()
             (add-to-list 'flymake-allowed-file-name-masks '("\\.erl\\'" flymake-syntaxerl))
             (add-to-list 'flymake-allowed-file-name-masks '("\\.hrl\\'" flymake-syntaxerl))
             (add-to-list 'flymake-allowed-file-name-masks '("\\.app\\'" flymake-syntaxerl))
             (add-to-list 'flymake-allowed-file-name-masks '("\\.app.src\\'" flymake-syntaxerl))
             (add-to-list 'flymake-allowed-file-name-masks '("\\.config\\'" flymake-syntaxerl))
             (add-to-list 'flymake-allowed-file-name-masks '("\\.rel\\'" flymake-syntaxerl))
             (add-to-list 'flymake-allowed-file-name-masks '("\\.script\\'" flymake-syntaxerl))
             (add-to-list 'flymake-allowed-file-name-masks '("\\.escript\\'" flymake-syntaxerl))

             ;; should be the last.
             (flymake-mode 1)
             ))
(provide 'init-erlang)
