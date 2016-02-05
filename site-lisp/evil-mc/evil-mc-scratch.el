;;; evil-mc-scratch.el --- Functions used during development

;;; Commentary:

;;; Code:

;; (global-evil-mc-mode  1)
;; (global-evil-mc-mode -1)

;; (evil-mc-mode  1)
;; (evil-mc-mode -1)

(defun evil-mc-clear-buffer-undo-list ()
  "Clear the `buffer-undo-list'."
  (interactive)
  (setq buffer-undo-list nil))

(defun evil-mc-clear-buffer-undo-tree ()
  "Clear the `buffer-undo-tree'."
  (interactive)
  (setq buffer-undo-tree nil))

(defun evil-mc-remove-all-overlays ()
  "Remove all overlays."
  (interactive)
  (remove-overlays)
  (setq evil-mc-cursor-list nil))

(defun evil-mc-insert-current-date-at-each-cursor ()
  "Insert the current date at each cursor position."
  (interactive)
  (evil-mc-execute-for-all-cursors
   (lambda (cursor)
     (insert-string
      (format-time-string "%d/%m/%Y" (current-time))))))

(defun evil-mc-change-num-at-each-cursor (change-cmd)
  "Run CHANGE-CMD that changes the number at cursor."
  (evil-mc-make-and-goto-first-cursor)
  (evil-mc-execute-for-all-cursors
   (lambda (cursor)
     (let ((index (evil-mc-get-cursor-property cursor :index)))
       (funcall change-cmd index)))))

(defun evil-mc-inc-num-at-each-cursor ()
  "Increment the number at each active cursor by the index amount."
  (interactive)
  (evil-mc-change-num-at-each-cursor 'evil-numbers/inc-at-pt))

(defun evil-mc-dec-num-at-each-cursor ()
  "Decrement the number at each active cursor by the index amount."
  (interactive)
  (evil-mc-change-num-at-each-cursor 'evil-numbers/dec-at-pt))

(provide 'evil-mc-scratch)

;;; evil-mc-scratch.el ends here
