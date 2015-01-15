(autoload 'smex "smex" nil t)
;; (smex-initialize) ; Can be omitted. This might cause a (minimal) delay
                  ; when Smex is auto-initialized on its first run.

;; Please note "M-x" doesnot work in GUI Emacs 24.4!
;; This is evil's bug
;; https://bitbucket.org/lyro/evil/issue/437/m-x-is-undefined-in-emacs-244
(global-set-key (kbd "M-x") 'smex)
(global-set-key (kbd "M-X") 'smex-major-mode-commands)
;; This is your old M-x.
(global-set-key (kbd "C-c C-c M-x") 'execute-extended-command)

(provide 'init-smex)
