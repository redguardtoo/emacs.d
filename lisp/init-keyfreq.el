(require 'keyfreq)

(defun turnon-keyfreq-mode ()
  (interactive)
  (keyfreq-mode 1)
  (keyfreq-autosave-mode 1))

(defun turnoff-keyfreq-mode ()
  (interactive)
  (keyfreq-mode -1)
  (keyfreq-autosave-mode -1))

(setq keyfreq-excluded-commands
      '(
        abort-recursive-edit
        backward-char
        backward-word
        clipboard-kill-ring-save
        company-complete-common
        company-complete-number
        company-complete-selection
        company-ignore
        delete-backward-char
        describe-variable
        erase-message-buffer
        eval-buffer
        evil-a-WORD
        evil-append
        evil-backward-char
        evil-backward-word-begin
        evil-change
        evil-change-line
        evil-delete
        evil-delete-backward-char-and-join
        evil-delete-char
        evil-delete-line
        evil-emacs-state
        evil-end-of-line
        evil-escape-emacs-state
        evil-escape-insert-state
        evil-escape-isearch
        evil-escape-minibuffer
        evil-escape-visual-state
        evil-ex
        evil-ex-command
        evil-ex-delete-backward-char
        evil-exit-visual-state
        evil-find-char
        evil-first-non-blank
        evil-force-normal-state
        evil-forward-char
        evil-forward-word-begin
        evil-forward-word-end
        evil-goto-first-line
        evil-goto-line
        evil-indent
        evil-insert
        evil-join
        evil-next-line
        evil-next-visual-line
        evil-normal-state
        evil-open-below
        evil-paste-after
        evil-previous-line
        evil-previous-visual-line
        evil-replace
        evil-ret
        evil-scroll-page-down
        evil-scroll-page-up
        evil-search-forward
        evil-search-next
        evil-search-word-forward
        evil-substitute
        evil-visual-char
        evil-visual-line
        evil-yank
        exit-minibuffer
        forward-char
        forward-word
        helm-next-line
        helm-previous-line
        ido-complete
        ido-delete-backward-updir
        ido-exit-minibuffer
        ido-switch-buffer
        indent-new-comment-line
        isearch-abort
        isearch-backward-regexp
        isearch-delete-char
        isearch-exit
        isearch-forward-regexp
        isearch-printing-char
        isearch-repeat-forward
        ispell-minor-check
        ivy-backward-delete-char
        ivy-done
        ivy-next-line
        ivy-previous-line
        keyboard-escape-quit
        keyboard-quit
        keyfreq-mode
        keyfreq-save-now
        keyfreq-show
        minibuffer-complete
        minibuffer-complete-and-exit
        minibuffer-keyboard-quit
        mwheel-scroll
        newline-and-indent
        next-history-element
        next-line
        org-beginning-of-line
        org-ctrl-c-ctrl-c
        org-cycle
        org-end-of-line
        org-return
        org-self-insert-command
        paredit-backward-delete
        paredit-backward-kill-word
        paredit-close-round
        paredit-newline
        paredit-open-round
        paredit-semicolon
        previous-history-element
        previous-line
        quit-window
        save-buffer
        save-buffer
        save-buffers-kill-terminal
        scroll-down-command
        scroll-up-command
        select-window-1
        select-window-2
        select-window-3
        select-window-4
        self-insert-command
        smarter-move-beginning-of-line
        smex
        suspend-frame
        term-send-raw
        turnon-keyfreq-mode
        undefined ;; lambda function
        undo-tree-redo
        undo-tree-undo
        yas-expand
        yas-next-field-or-maybe-expand
        ))

(unless (file-exists-p (file-truename keyfreq-file))
  (with-temp-buffer
    (insert "()")
    (write-file (file-truename keyfreq-file))))

;; And use keyfreq-show to see how many times you used a command.
;; comment out below line if there is performance impact
(turnon-keyfreq-mode)

(provide 'init-keyfreq)
