;; Use C-f during file selection to switch to regular find-file
(require 'flx-ido)
(ido-mode 'file)  ; use 'buffer rather than t to use only buffer switching
(flx-ido-mode 1)
;; disable ido faces to see flx highlights.
(setq ido-enable-flex-matching t)
(setq ido-use-faces nil)
(setq ido-use-filename-at-point nil)
(setq ido-auto-merge-work-directories-length 0)
(setq ido-use-virtual-buffers t)
;; @see https://github.com/lewang/flx
(setq flx-ido-threshold 10000)
;; Allow the same buffer to be open in different frames
(setq ido-default-buffer-method 'selected-window)

;; disable ido for certain commands,
;; @see http://stackoverflow.com/questions/6771664/disable-ido-mode-for-specific-commands
(defadvice ido-read-buffer (around ido-read-buffer-possibly-ignore activate)
  "Check to see if use wanted to avoid using ido"
  (if (eq (get this-command 'ido) 'ignore)
      (let ((read-buffer-function nil))
        (run-hook-with-args 'ido-before-fallback-functions 'read-buffer)
        (setq ad-return-value (apply 'read-buffer (ad-get-args 0))))
    ad-do-it))
(put 'shell 'ido 'ignore)
(put 'ffap-alternate-file 'ido 'ignore)
(put 'tmm-menubar 'ido 'ignore)
(put 'dired-do-copy 'ido 'ignore)
(put 'dired-do-rename 'ido 'ignore)
(put 'vc-copy-file-and-rename-buffer 'ido 'ignore)
(put 'dired-create-directory 'ido 'ignore)
(put 'copy-file-and-rename-buffer 'ido 'ignore)
(put 'rename-file-and-buffer 'ido 'ignore)
(put 'w3m-goto-url 'ido 'ignore)
(put 'ido-find-file 'ido 'ignore)
(put 'ido-edit-input 'ido 'ignore)
(put 'read-file-name 'ido 'ignore)
(put 'dired-create-directory 'ido 'ignore)
(put 'minibuffer-completion-help 'ido 'ignore)
(put 'minibuffer-complete 'ido 'ignore)
(put 'c-set-offset 'ido 'ignore)
(put 'rgrep 'ido 'ignore)
(put 'dired-create-directory 'ido 'ignore)

(provide 'init-ido)
