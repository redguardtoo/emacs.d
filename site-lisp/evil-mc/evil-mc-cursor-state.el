;;; evil-mc-cursor-state.el --- State saved for each fake cursor

;;; Commentary:

;; This file contains functions to interact with the state of a fake cursor

(require 'evil-mc-common)

;;; Code:

(defun evil-mc-get-cursor-variables (&optional categories)
  "Gets the cursor variable names associated with CATEGORIES.
If CATEGORIES is nil return all cursor variables."
  (cond ((null categories)
         (apply 'append (mapcar 'cdr evil-mc-cursor-variables)))
        ((atom categories)
         (evil-mc-get-object-property evil-mc-cursor-variables categories))
        (t (apply 'append (mapcar (lambda (category)
                                    (evil-mc-get-object-property
                                     evil-mc-cursor-variables
                                     category))
                                  categories)))))

(defun evil-mc-get-cursor-property (cursor name)
  "Return the value of the CURSOR property with NAME."
  (when cursor (evil-mc-get-object-property cursor name)))

(defun evil-mc-put-cursor-property (cursor &rest properties)
  "Return a new CURSOR that has one or more PROPERTIES set to the specified values."
  (apply 'evil-mc-put-object-property (cons cursor properties)))

(defun evil-mc-get-cursor-properties (cursor properties)
  "Return the values of all CURSOR PROPERTIES as a list."
  (when cursor
    (mapcar (lambda (prop) (evil-mc-get-object-property cursor prop))
            properties)))

(defun evil-mc-get-cursor-overlay (cursor)
  "Get the overlay for CURSOR."
  (evil-mc-get-cursor-property cursor 'overlay))

(defun evil-mc-put-cursor-overlay (cursor overlay)
  "Set the overlay for CURSOR to OVERLAY."
  (evil-mc-put-cursor-property cursor 'overlay overlay))

(defun evil-mc-get-cursor-last-position (cursor)
  "Get the last-position for CURSOR."
  (evil-mc-get-cursor-property cursor 'last-position))

(defun evil-mc-put-cursor-last-position (cursor last-position)
  "Set the last-position for CURSOR to LAST-POSITION."
  (evil-mc-put-cursor-property cursor 'last-position last-position))

(defun evil-mc-get-cursor-undo-stack (cursor)
  "Get the undo-stack for CURSOR."
  (evil-mc-get-cursor-property cursor 'undo-stack))

(defun evil-mc-put-cursor-undo-stack (cursor undo-stack)
  "Set the undo-stack for CURSOR to UNDO-STACK."
  (evil-mc-put-cursor-property cursor 'undo-stack undo-stack))

(defun evil-mc-get-cursor-undo-stack-pointer (cursor)
  "Get the undo-stack-pointer for CURSOR."
  (evil-mc-get-cursor-property cursor 'undo-stack-pointer))

(defun evil-mc-put-cursor-undo-stack-pointer (cursor undo-stack-pointer)
  "Set the undo-stack-pointer for CURSOR to UNDO-STACK-POINTER."
  (evil-mc-put-cursor-property cursor 'undo-stack-pointer undo-stack-pointer))

(defun evil-mc-get-cursor-region (cursor)
  "Get the region for CURSOR."
  (evil-mc-get-cursor-property cursor 'region))

(defun evil-mc-put-cursor-region (cursor region)
  "Set the region for CURSOR to REGION."
  (evil-mc-put-cursor-property cursor 'region region))

(defun evil-mc-get-cursor-kill-ring (cursor)
  "Get the `kill-ring' for CURSOR."
  (evil-mc-get-cursor-property cursor 'kill-ring))

(defun evil-mc-put-cursor-kill-ring (cursor kill-ring)
  "Set the `kill-ring' for CURSOR to KILL-RING."
  (evil-mc-put-cursor-property cursor 'kill-ring kill-ring))

(defun evil-mc-get-cursor-kill-ring-yank-pointer (cursor)
  "Get the `kill-ring-yank-pointer' for CURSOR."
  (evil-mc-get-cursor-property
   cursor 'kill-ring-yank-pointer))

(defun evil-mc-put-cursor-kill-ring-yank-pointer (cursor kill-ring-yank-pointer)
  "Set the `kill-ring-yank-pointer' for CURSOR to KILL-RING-YANK-POINTER."
  (evil-mc-put-cursor-property
   cursor 'kill-ring-yank-pointer kill-ring-yank-pointer))

(defun evil-mc-get-cursor-temporary-goal-column (cursor)
  "Get the temporary-goal-column for CURSOR."
  (evil-mc-get-cursor-property cursor 'temporary-goal-column))

(defun evil-mc-put-cursor-temporary-goal-column (cursor temporary-goal-column)
  "Set the temporary-goal-column for CURSOR to TEMPORARY-GOAL-COLUMN."
  (evil-mc-put-cursor-property cursor 'temporary-goal-column temporary-goal-column))

(defun evil-mc-get-cursor-evil-markers-alist (cursor)
  "Get the evil-markers-alist for CURSOR."
  (evil-mc-get-cursor-property cursor 'evil-markers-alist))

(defun evil-mc-put-cursor-evil-markers-alist (cursor evil-markers-alist)
  "Set the evil-markers-alist for CURSOR to EVIL-MARKERS-ALIST."
  (evil-mc-put-cursor-property cursor 'evil-markers-alist evil-markers-alist))

(defun evil-mc-get-cursor-evil-jump-list (cursor)
  "Get the evil-jump-list for CURSOR."
  (evil-mc-get-cursor-property cursor 'evil-jump-list))

(defun evil-mc-put-cursor-evil-jump-list (cursor evil-jump-list)
  "Set the evil-jump-list for CURSOR to EVIL-JUMP-LIST."
  (evil-mc-put-cursor-property cursor 'evil-jump-list evil-jump-list))

(defun evil-mc-get-cursor-mark-ring (cursor)
  "Get the `mark-ring' for CURSOR."
  (evil-mc-get-cursor-property cursor 'mark-ring))

(defun evil-mc-put-cursor-mark-ring (cursor mark-ring)
  "Set the `mark-ring' for CURSOR to MARK-RING."
  (evil-mc-put-cursor-property cursor 'mark-ring mark-ring))

(defun evil-mc-get-cursor-mark-active (cursor)
  "Get the `mark-active' for CURSOR."
  (evil-mc-get-cursor-property cursor 'mark-active))

(defun evil-mc-put-cursor-mark-active (cursor mark-active)
  "Set the `mark-active' for CURSOR to MARK-ACTIVE."
  (evil-mc-put-cursor-property cursor 'mark-active mark-active))

(defun evil-mc-get-cursor-start (cursor)
  "Get the CURSOR overlay start."
  (when cursor
    (overlay-start (evil-mc-get-cursor-overlay cursor))))

(defun evil-mc-get-cursor-end (cursor)
  "Get the CURSOR overlay end."
  (when cursor
    (overlay-end (evil-mc-get-cursor-overlay cursor))))

(defun evil-mc-delete-cursor-overlay (cursor)
  "Deletes the overlay associated with CURSOR."
  (when cursor
    (let ((overlay (evil-mc-get-cursor-overlay cursor)))
      (when overlay (delete-overlay overlay)))))

(provide 'evil-mc-cursor-state)

;;; evil-mc-cursor-state.el ends here
