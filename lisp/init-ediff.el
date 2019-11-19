;; -*- coding: utf-8; lexical-binding: t; -*-

(defvar my-ediff-panel-name nil)

(when (and (boundp 'startup-now) startup-now)

  ;; remove `org-mode' from `auto-mode-alist'. So nodes in org file do NOT collapse at all
  (setq auto-mode-alist  (rassq-delete-all 'org-mode auto-mode-alist))
  ;; associate simpler major mode with org file instead
  (add-auto-mode 'outline-mode "\\.org\\(_archive\\)?$")


  (defmacro my-ediff-command (cmd &optional no-arg)
    `(lambda (&optional arg)
       (interactive "P")
       (let* ((w (get-buffer-window)))
         ;; go to panel window
         (select-window (get-buffer-window my-ediff-panel-name))
         ;; execute ediff command, ignore any error
         (condition-case e
             (if ,no-arg (funcall ,cmd) (funcall ,cmd arg))
           (error
            (message "%s" (error-message-string e))))
         ;; back to original window
         (select-window w))))

  (unless (featurep 'ediff) (require 'ediff))

  ;; @see https://stackoverflow.com/a/29757750/245363
  (defun ediff-copy-both-to-C (&optional arg)
    "Copy code from both A and B to C."
    (interactive)
    (ediff-copy-diff ediff-current-difference nil 'C nil
                     (concat
                      (ediff-get-region-contents ediff-current-difference 'A ediff-control-buffer)
                      (ediff-get-region-contents ediff-current-difference 'B ediff-control-buffer))))

  (my-space-leader-def
    "a" (lambda () (interactive) (jump-to-register ?a))
    "n" (my-ediff-command 'ediff-next-difference)
    "p" (my-ediff-command 'ediff-previous-difference)
    "r" (my-ediff-command 'ediff-restore-diff-in-merge-buffer)
    "R" (my-ediff-command 'ediff-revert-buffers-then-recompute-diffs) ; press "1-space-R" to revert without confirmation
    "xa" (lambda () (interactive) (save-buffers-kill-terminal t)) ; similar to vim
    ;; use 1 3 as hotkey to be consistent with vim
    "1" (my-ediff-command 'ediff-copy-A-to-C)
    "3" (my-ediff-command 'ediff-copy-B-to-C)
    "b" (my-ediff-command 'ediff-copy-both-to-C))

  (defun ediff-startup-hook-setup ()
    ;; hide control panel if it's current buffer
    (when (string-match-p (setq my-ediff-panel-name (buffer-name))
                          "\*Ediff Control Panel.*\*")
      ;; load color theme for merge
      (load-theme 'deeper-blue t)
      ;; move to the first difference
      (ediff-next-difference)
      ;; move to the merged buffer window
      (winum-select-window-by-number 3)
      ;; save the windows layout
      (window-configuration-to-register ?a)))

  (add-hook 'ediff-startup-hook 'ediff-startup-hook-setup))

(provide 'init-ediff)
