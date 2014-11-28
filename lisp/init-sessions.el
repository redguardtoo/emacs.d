;; save a list of open files in ~/.emacs.d/.emacs.desktop
;; save the desktop file automatically if it already exists
(setq desktop-path '("~/.emacs.d"))
(setq desktop-save 'if-exists)
(desktop-save-mode 1)
(defadvice desktop-read (around trace-desktop-errors)
  (let ((debug-on-error t))
    ad-do-it))


;;----------------------------------------------------------------------------
;; Restore histories and registers after saving
;;----------------------------------------------------------------------------
(setq session-save-file (expand-file-name "~/.emacs.d/.session"))
(add-hook 'after-init-hook 'session-initialize)

;; save a bunch of variables to the desktop file
;; for lists specify the len of the maximal saved data also
(setq desktop-globals-to-save
      (append '((extended-command-history . 128)
                (file-name-history        . 128)
                (ido-last-directory-list  . 128)
                (ido-work-directory-list  . 128)
                (ido-work-file-list       . 128)
                (grep-history             . 128)
                (compile-history          . 128)
                (minibuffer-history       . 128)
                (query-replace-history    . 128)
                (read-expression-history  . 128)
                (regexp-history           . 128)
                (regexp-search-ring       . 128)
                (search-ring              . 128)
                (comint-input-ring        . 128)
                (shell-command-history    . 128)
                (evil-ex                  . 128)
                desktop-missing-file-warning
                register-alist)))

(provide 'init-sessions)
