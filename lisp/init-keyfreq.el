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
                                  evil-next-line
                                  evil-previous-line
                                  evil-forward-char
                                  evil-backward-char
                                  self-insert-command
                                  evil-scroll-page-down
                                  evil-scroll-page-up
                                  evil-find-char
                                  save-buffer
                                  evil-escape-minibuffer
                                  minibuffer-complete
                                  minibuffer-keyboard-quit
                                  evil-normal-state
                                  evil-forward-word-begin
                                  evil-backward-word-begin
                                  evil-forward-word-end
                                  evil-search-word-forward
                                  evil-search-next
                                  evil-search-forward
                                  evil-substitute
                                  evil-paste-after
                                  evil-open-below
                                  evil-end-of-line
                                  evil-delete-char
                                  evil-emacs-state
                                  evil-indent
                                  evil-insert
                                  evil-yank
                                  evil-delete
                                  evil-escape-emacs-state
                                  evil-escape-visual-state
                                  evil-escape-insert-state
                                  evil-goto-first-line
                                  evil-goto-line
                                  evil-visual-line
                                  evil-visual-char
                                  evil-join
                                  evil-replace
                                  evil-change
                                  evil-append
                                  evil-ex
                                  evil-delete-backward-char-and-join
                                  evil-ret
                                  evil-escape-isearch
                                  mwheel-scroll
                                  abort-recursive-edit
                                  quit-window
                                  forward-word
                                  backward-word
                                  org-cycle
                                  org-self-insert-command
                                  org-end-of-line
                                  org-beginning-of-line
                                  org-return
                                  scroll-up-command
                                  scroll-down-command
                                  isearch-forward-regexp
                                  isearch-backward-regexp
                                  isearch-delete-char
                                  isearch-repeat-forward
                                  minibuffer-complete-and-exit
                                  previous-history-element
                                  next-history-element
                                  paredit-semicolon
                                  paredit-backward-delete
                                  paredit-open-round
                                  paredit-close-round
                                  paredit-newline
                                  paredit-backward-kill-word
                                  clipboard-kill-ring-save
                                  smarter-move-beginning-of-line
                                  company-ignore
                                  company-complete-common
                                  company-complete-selection
                                  company-complete-number
                                  undefined ;; lambda function
                                  delete-backward-char
                                  next-line
                                  previous-line
                                  forward-char
                                  backward-char
                                  smex
                                  suspend-frame
                                  describe-variable
                                  keyboard-quit
                                  keyboard-escape-quit
                                  newline-and-indent
                                  indent-new-comment-line
                                  erase-message-buffer
                                  select-window-1
                                  select-window-2
                                  select-window-3
                                  select-window-4
                                  yas-expand
                                  isearch-printing-char
                                  isearch-exit
                                  save-buffer
                                  eval-buffer
                                  undo-tree-undo
                                  undo-tree-redo
                                  keyfreq-show
                                  keyfreq-save-now
                                  keyfreq-mode
                                  turnon-keyfreq-mode
                                  save-buffers-kill-terminal
                                  exit-minibuffer
                                  ido-complete
                                  ido-delete-backward-updir
                                  ido-switch-buffer
                                  ido-exit-minibuffer))

(unless (file-exists-p (file-truename keyfreq-file))
  (with-temp-buffer
    (insert "()")
    (write-file (file-truename keyfreq-file))))

;; And use keyfreq-show to see how many times you used a command.
;; comment out below line if there is performance impact
(turnon-keyfreq-mode)

(provide 'init-keyfreq)
