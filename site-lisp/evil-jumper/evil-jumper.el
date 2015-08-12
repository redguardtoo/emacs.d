;;; evil-jumper.el --- Jump like vimmers do!

;; Copyright (C) 2014 by Bailey Ling
;; Author: Bailey Ling
;; URL: https://github.com/bling/evil-jumper
;; Filename: evil-jumper.el
;; Description: Jump like vimmers do!
;; Created: 2014-07-01
;; Version: 0.2.1
;; Keywords: evil vim jumplist jump list
;; Package-Requires: ((evil "0"))
;;
;; This file is not part of GNU Emacs.
;;
;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the GNU General Public License as
;; published by the Free Software Foundation; either version 3, or
;; (at your option) any later version.
;;
;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;; General Public License for more details.
;;
;; You should have received a copy of the GNU General Public License
;; along with this program; see the file COPYING.  If not, write to
;; the Free Software Foundation, Inc., 51 Franklin Street, Fifth
;; Floor, Boston, MA 02110-1301, USA.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Commentary:
;;
;; evil-jumper is an add-on for evil-mode which replaces the
;; implementation of the jump list such that it mimics more closely
;; with Vim's behavior. Specifically, it will jump across buffer
;; boundaries and revive dead buffers if necessary. The jump list can
;; also be persisted to a file and restored between sessions.
;;
;; Install:
;;
;; (require 'evil-jumper)
;;
;; Usage:
;;
;; (global-evil-jumper-mode)

;;; Code:

(require 'cl)
(require 'evil)

(defgroup evil-jumper nil
  "evil-jumper configuration options."
  :prefix "evil-jumper"
  :group 'evil)

(defcustom evil-jumper-max-length 100
  "The maximum number of jumps to keep track of."
  :type 'integer
  :group 'evil-jumper)

(defcustom evil-jumper-auto-center nil
  "Auto-center the line after jumping."
  :type 'boolean
  :group 'evil-jumper)

(defcustom evil-jumper-ignored-file-patterns '("COMMIT_EDITMSG" "TAGS")
  "A list of pattern regexps to match on the file path to exclude from being included in the jump list."
  :type '(repeat string)
  :group 'evil-jumper)

(defcustom evil-jumper-file nil
  "The location of the file to save/load the jump list."
  :type 'string
  :group 'evil-jumper)

(defcustom evil-jumper-auto-save-interval 0
  "If positive, specifies the interval in seconds to persist the jump list.

Note: The value of `evil-jumper-file' must also be non-nil."
  :type 'integer
  :group 'evil-jumper)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defvar evil-jumper--jumping nil)
(defvar evil-jumper--debug nil)
(defvar evil-jumper--wired nil)

(defvar
  evil-jumper--window-jumps
  (make-hash-table)
  "Hashtable which stores all jumps on a per window basis.")

(defstruct evil-jumper-jump
  jumps
  (idx -1))

(defun evil-jumper--message (format &rest args)
  (when evil-jumper--debug
    (setq format (concat "evil-jumper: " format))
    (apply 'message format args)))

(defun evil-jumper--get-current (&optional window)
  (unless window
    (setq window (frame-selected-window)))
  (let* ((jump-struct (gethash window evil-jumper--window-jumps)))
    (unless jump-struct
      (setq jump-struct (make-evil-jumper-jump))
      (puthash window jump-struct evil-jumper--window-jumps))
    jump-struct))

(defun evil-jumper--get-window-jump-list ()
  (let ((struct (evil-jumper--get-current)))
    (evil-jumper-jump-jumps struct)))

(defun evil-jumper--set-window-jump-list (list)
  (let ((struct (evil-jumper--get-current)))
    (setf (evil-jumper-jump-jumps struct) list)))

(defun evil-jumper--read-file ()
  "Restores the jump list from the persisted file."
  (when (file-exists-p evil-jumper-file)
    (let ((lines (with-temp-buffer
                   (insert-file-contents evil-jumper-file)
                   (split-string (buffer-string) "\n" t)))
          (jumps nil))
      (dolist (line lines)
        (let* ((parts (split-string line " "))
               (pos (string-to-number (car parts)))
               (file-name (cadr parts)))
          (push (list pos file-name) jumps)))
      (evil-jumper--set-window-jump-list jumps))))

(defun evil-jumper--write-file ()
  "Saves the current contents of the jump list to a persisted file."
  (with-temp-file evil-jumper-file
    (let ((jumps (evil-jumper--get-window-jump-list)))
      (dolist (jump jumps)
        (let ((pos (car jump))
              (file-name (cadr jump)))
          (when (file-exists-p file-name)
            (insert (format "%d" pos))
            (insert " ")
            (insert file-name)
            (insert "\n")))))))

(defun evil-jumper--jump-to-index (idx)
  (let ((target-list (evil-jumper--get-window-jump-list)))
    (when (and (< idx (length target-list))
               (>= idx 0))
      (setf (evil-jumper-jump-idx (evil-jumper--get-current)) idx)
      (let* ((place (nth idx target-list))
             (pos (car place))
             (file-name (cadr place)))
        (setq evil-jumper--jumping t)
        (if (equal file-name "*scratch*")
            (switch-to-buffer file-name)
          (find-file file-name))
        (setq evil-jumper--jumping nil)
        (goto-char pos)
        (when evil-jumper-auto-center
          (recenter))))))

(defun evil-jumper--push ()
  "Pushes the current cursor/file position to the jump list."
  (let ((target-list (evil-jumper--get-window-jump-list)))
    (while (> (length target-list) evil-jumper-max-length)
      (nbutlast target-list 1))
    (let ((file-name (buffer-file-name))
          (buffer-name (buffer-name))
          (current-pos (point))
          (first-pos nil)
          (first-file-name nil)
          (excluded nil))
      (when (and (not file-name) (equal buffer-name "*scratch*"))
        (setq file-name buffer-name))
      (when file-name
        (dolist (pattern evil-jumper-ignored-file-patterns)
          (when (string-match-p pattern file-name)
            (setq excluded t)))
        (unless excluded
          (when target-list
            (setq first-pos (caar target-list))
            (setq first-file-name (car (cdar target-list))))
          (unless (and (equal first-pos current-pos)
                       (equal first-file-name file-name))
            (push `(,current-pos ,file-name) target-list)))))
    (evil-jumper--message "%s %s" (selected-window) (car target-list))
    (evil-jumper--set-window-jump-list target-list)))

(defun evil-jumper--set-jump ()
  (unless evil-jumper--jumping
    ;; clear out intermediary jumps when a new one is set
    (let* ((struct (evil-jumper--get-current))
           (target-list (evil-jumper-jump-jumps struct))
           (idx (evil-jumper-jump-idx struct)))
      (nbutlast target-list idx)
      (setf (evil-jumper-jump-jumps struct) target-list)
      (setf (evil-jumper-jump-idx struct) -1))
    (evil-jumper--push)))

(evil-define-motion evil-jumper/backward (count)
  (let* ((count (or count 1))
         (struct (evil-jumper--get-current))
         (idx (evil-jumper-jump-idx struct)))
    (evil-motion-loop (nil count)
      (when (= idx -1)
        (setq idx (+ idx 1))
        (setf (evil-jumper-jump-idx struct) idx)
        (evil-jumper--push))
      (evil-jumper--jump-to-index (+ idx 1)))))

(evil-define-motion evil-jumper/forward (count)
  (let* ((count (or count 1))
         (struct (evil-jumper--get-current))
         (idx (evil-jumper-jump-idx struct)))
    (evil-motion-loop (nil count)
      (evil-jumper--jump-to-index (- idx 1)))))

(defun evil-jumper--window-configuration-hook (&rest args)
  (let* ((window-list (window-list))
         (existing-window (selected-window))
         (new-window (previous-window)))
    (when (and (not (eq existing-window new-window))
               (> (length window-list) 1))
      (let* ((target-jump-struct (evil-jumper--get-current new-window))
             (target-jump-count (length (evil-jumper-jump-jumps target-jump-struct))))
        (if (evil-jumper-jump-jumps target-jump-struct)
            (evil-jumper--message "target window %s already has %s jumps" new-window target-jump-count)
          (evil-jumper--message "new target window detected; copying %s to %s" existing-window new-window)
          (let* ((source-jump-struct (evil-jumper--get-current existing-window))
                 (source-list (evil-jumper-jump-jumps source-jump-struct)))
            (when (= (length (evil-jumper-jump-jumps target-jump-struct)) 0)
              (setf (evil-jumper-jump-idx target-jump-struct) (evil-jumper-jump-idx source-jump-struct))
              (setf (evil-jumper-jump-jumps target-jump-struct) (copy-sequence source-list)))))))
    ;; delete obsolete windows
    (maphash (lambda (key val)
               (unless (member key window-list)
                 (evil-jumper--message "removing %s" key)
                 (remhash key evil-jumper--window-jumps)))
             evil-jumper--window-jumps)))

(defun evil-jumper--init-file ()
  (when (and (not evil-jumper--wired)
             evil-jumper-file)
    (evil-jumper--read-file)
    (defadvice save-buffers-kill-emacs (before evil-jumper--save-buffers-kill-emacs activate)
      (evil-jumper--write-file))
    (when (> evil-jumper-auto-save-interval 0)
      (run-with-timer evil-jumper-auto-save-interval evil-jumper-auto-save-interval #'evil-jumper--write-file))
    (setq evil-jumper--wired t)))

;;;###autoload
(define-minor-mode evil-jumper-mode
  "Global minor mode for vim jumplist emulation."
  :global t
  :keymap (let ((map (make-sparse-keymap)))
            (evil-define-key 'normal map (kbd "C-o") #'evil-jumper/backward)
            (when evil-want-C-i-jump
              (evil-define-key 'normal map (kbd "C-i") #'evil-jumper/forward))
            map)
  (if evil-jumper-mode
      (progn
        (evil-jumper--init-file)
        (add-hook 'next-error-hook #'evil-jumper--set-jump)
        (add-hook 'window-configuration-change-hook #'evil-jumper--window-configuration-hook)
        (defadvice evil-set-jump (after evil-jumper--evil-set-jump activate)
          (evil-jumper--set-jump))
        (defadvice switch-to-buffer (before evil-jumper--switch-to-buffer activate)
          (evil-jumper--set-jump))
        (defadvice find-tag-noselect (before evil-jumper--find-tag-noselect activate)
          (evil-jumper--set-jump)))
    (progn
      (remove-hook 'next-error-hook #'evil-jumper--set-jump)
      (remove-hook 'window-configuration-change-hook #'evil-jumper--window-configuration-hook)
      (ad-remove-advice 'evil-set-jump 'after 'evil-jumper--evil-set-jump)
      (ad-remove-advice 'switch-to-buffer 'before 'evil-jumper--switch-to-buffer)
      (ad-remove-advice 'find-tag-noselect 'before 'evil-jumper--find-tag-noselect)))
  (evil-normalize-keymaps))

;;;###autoload
(defun turn-on-evil-jumper-mode ()
  "Turns on vim jumplist emulation."
  (interactive)
  (evil-jumper-mode t))

;;;###autoload
(defun turn-off-evil-jumper-mode ()
  "Turns off vim jumplist emulation."
  (interactive)
  (evil-jumper-mode -1))

;;;###autoload
(defalias 'global-evil-jumper-mode 'evil-jumper-mode)

(provide 'evil-jumper)

;;; evil-jumper.el ends here
