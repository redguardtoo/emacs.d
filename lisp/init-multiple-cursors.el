(defmacro set-evil-move-cursor-back (v)
  `(if (boundp 'evil-move-cursor-back)
    (setq evil-move-cursor-back ,v)))

(eval-after-load 'multiple-cursors-core
  '(progn
     ;; setup `evil-move-cursor-back' temporarily
     (defadvice mc/mark-all-like-this-dwim (before mc/mark-all-like-this-dwim-before-hack activate)
       (set-evil-move-cursor-back nil))
     (defadvice mc/mark-all-like-this-in-defun (before mc/mark-all-like-this-in-defun-before-hack activate)
       (set-evil-move-cursor-back nil))
     ;; restore `evil-move-cursor-back'
     (defadvice multiple-cursors-mode (before multiple-cursors-mode-before-hack activate)
       (if (= 0 (ad-get-arg 0)) (set-evil-move-cursor-back t)))
     (defadvice mc/keyboard-quit (before mc/keyboard-quit-before-hack activate)
       (set-evil-move-cursor-back t))

     (nconc mc--default-cmds-to-run-for-all
            '(evil-append
              evil-first-non-blank
              evil-first-non-blank-of-visual-line
              evil-end-of-line
              evil-end-of-visual-line
              evil-delete
              evil-delete-char
              evil-delete-backward-char-and-join
              evil-visual-char
              evil-visual-block
              evil-yank
              evil-end-of-line
              evil-exit-visual-state
              evil-paste-pop-next
              evil-surround-region
              evil-substitute
              evil-paste-after
              evil-paste-before
              evil-paste-from-register
              evil-replace
              evil-repeat
              autopair-backspace
              sp--self-insert-command
              c-electric-backspace
              evil-search-next
              my-M-x
              evil-ret
              evil-forward-char
              evil-backward-char
              evil-forward-word-begin
              evil-backward-word-begin
              evil-forward-word-end
              evil-backward-word-end
              evil-forward-WORD-begin
              evil-backward-WORD-begin
              evil-forward-WORD-end
              evil-backward-WORD-end
              evil-change
              evil-change-line
              evil-next-line
              evil-previous-line
              evil-find-char
              evil-find-char-backward
              evil-find-char-to
              evil-find-char-to-backward
              evil-force-normal-state
              evil-insert
              evil-insert-line
              evil-join
              evil-open-above
              evil-open-below
              evil-normal-state
              evil-normal-post-command
              evil-inner-tag
              yas-expand))
     (nconc mc--default-cmds-to-run-once
            '(evil-goto-mark-line
              counsel-M-x
              smex
              ivy-done
              hydra-launcher/body
              multiple-cursors-hydra/body
              multiple-cursors-hydra/mc/edit-lines-and-exit
              multiple-cursors-hydra/mc/mark-all-like-this-and-exit
              multiple-cursors-hydra/mc/mark-previous-like-this
              multiple-cursors-hydra/mc/mark-next-like-this
              multiple-cursors-hydra/mc/skip-to-previous-like-this
              multiple-cursors-hydra/mc/skip-to-next-like-this
              multiple-cursors-hydra/mc/unmark-previous-like-this
              multiple-cursors-hydra/mc/unmark-next-like-this
              multiple-cursors-hydra/nil))))

(provide 'init-multiple-cursors)
