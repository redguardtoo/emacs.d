(require 'keyfreq)

(defun turnon-keyfreq-mode ()
  (interactive)
  (keyfreq-mode 1)
  (keyfreq-autosave-mode 1))

(defun turnoff-keyfreq-mode ()
  (interactive)
  (keyfreq-mode -1)
  (keyfreq-autosave-mode -1))

(setq keyfreq-excluded-commands '(evil-next-visual-line
                                  evil-previous-visual-line
                                  evil-forward-char
                                  evil-backward-char
                                  self-insert-command
                                  save-buffer
                                  evil-escape-minibufferi
                                  smex
                                  evil-normal-state
                                  evil-forward-word-begin
                                  evil-backward-word-begin
                                  evil-open-below
                                  evil-end-of-line
                                  evil-indent
                                  evil-insert
                                  evil-join
                                  evil-change
                                  evil-append
                                  suspend-frame
                                  describe-variable
                                  keyboard-quit
                                  erase-message-buffer
                                  select-window-1
                                  select-window-2
                                  select-window-3
                                  select-window-4
                                  yas-expand
                                  isearch-printing-char
                                  save-buffer
                                  eval-buffer
                                  undo-tree-undo
                                  ido-switch-buffer
                                  ido-exit-minibuffer))

(unless (file-exists-p (file-truename keyfreq-file))
  (with-temp-buffer
    (insert "()")
    (write-file (file-truename keyfreq-file))))
;; And use keyfreq-show to see how many times you used a command.
(provide 'init-keyfreq)
