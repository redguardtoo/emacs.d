(require 'erlang-start)
(require 'flymake)
;; (setq flymake-log-level 3) ;; log is annoying

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

(defun my-setup-erlang ()
  (interactive)
  (unless (is-buffer-file-temp)
    (when (file-exists-p (file-truename "~/bin/syntaxerl"))
      (setq erlang-compile-extra-opts
            '(bin_opt_info debug_info (i . "../include") (i . "../deps") (i . "../../") (i . "../../../deps")))
      (setq erlang-compile-outdir "../ebin")
      ;; if the project is in a git directory, then ...
      (let (root-dir )
        (setq root-dir (locate-dominating-file (file-name-as-directory (file-name-directory buffer-file-name)) ".git"))
        (when (and root-dir (file-exists-p root-dir))
          (push '(i . (concat root-dir "include")) 'erlang-compile-outdir)
          (push '(i . (concat root-dir "deps")) 'erlang-compile-outdir)
          ;; define where put beam files.
          (setq erlang-compile-outdir (concat root-dir "ebin"))
          ))

      (add-to-list 'flymake-allowed-file-name-masks '("\\.erl\\'" flymake-syntaxerl))
      (add-to-list 'flymake-allowed-file-name-masks '("\\.hrl\\'" flymake-syntaxerl))
      (add-to-list 'flymake-allowed-file-name-masks '("\\.app\\'" flymake-syntaxerl))
      (add-to-list 'flymake-allowed-file-name-masks '("\\.app.src\\'" flymake-syntaxerl))
      (add-to-list 'flymake-allowed-file-name-masks '("\\.config\\'" flymake-syntaxerl))
      (add-to-list 'flymake-allowed-file-name-masks '("\\.rel\\'" flymake-syntaxerl))
      (add-to-list 'flymake-allowed-file-name-masks '("\\.script\\'" flymake-syntaxerl))
      (add-to-list 'flymake-allowed-file-name-masks '("\\.escript\\'" flymake-syntaxerl))
      ;; should be the last.
      (flymake-mode 1))))

(add-hook 'erlang-mode-hook 'my-setup-erlang)

(provide 'init-erlang)
