;;; elpy-refactor.el --- Refactoring mode for Elpy

;; Copyright (C) 2013  Jorgen Schaefer

;; Author: Jorgen Schaefer <contact@jorgenschaefer.de>
;; URL: https://github.com/jorgenschaefer/elpy

;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the GNU General Public License
;; as published by the Free Software Foundation; either version 3
;; of the License, or (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program. If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:

;; This file provides an interface, including a major mode, to use
;; refactoring options provided by the Rope library.

;;; Code:

;; We require elpy, but elpy loads us, so we shouldn't load it back.
;; (require 'elpy)

(defvar elpy-refactor-changes nil
  "Changes that will be commited on \\[elpy-refactor-commit].")
(make-variable-buffer-local 'elpy-refactor-current-changes)

(defvar elpy-refactor-window-configuration nil
  "The old window configuration. Will be restored after commit.")
(make-variable-buffer-local 'elpy-refactor-window-configuration)

(make-obsolete
 'elpy-refactor
 "Refactoring has been unstable and flakey, support will be dropped in the future."
 "elpy 1.5.0")
(defun elpy-refactor ()
  "Run the Elpy refactoring interface for Python code."
  (interactive)
  (save-some-buffers)
  (let* ((selection (elpy-refactor-select
                     (elpy-refactor-rpc-get-options)))
         (method (car selection))
         (args (cdr selection)))
    (when method
      (elpy-refactor-create-change-buffer
       (elpy-refactor-rpc-get-changes method args)))))

(defun elpy-refactor-select (options)
  "Show the user the refactoring options and let her choose one.

Depending on the chosen option, ask the user for further
arguments and build the argument.

Return a cons cell of the name of the option and the arg list
created."
  (let ((buf (get-buffer-create "*Elpy Refactor*"))
        (pos (vector (1- (point))
                     (ignore-errors
                       (1- (region-beginning)))
                     (ignore-errors
                       (1- (region-end)))))
        (inhibit-read-only t)
        (options (sort options
                       (lambda (a b)
                         (let ((cata (cdr (assq 'category a)))
                               (catb (cdr (assq 'category b))))
                           (if (equal cata catb)
                               (string< (cdr (assq 'description a))
                                        (cdr (assq 'description b)))
                             (string< cata catb))))))
        (key ?a)
        last-category
        option-alist)
    (with-current-buffer buf
      (erase-buffer)
      (dolist (option options)
        (let ((category (cdr (assq 'category option)))
              (description (cdr (assq 'description option)))
              (name (cdr (assq 'name option)))
              (args (cdr (assq 'args option))))
          (when (not (equal category last-category))
            (when last-category
              (insert "\n"))
            (insert (propertize category 'face 'bold) "\n")
            (setq last-category category))
          (insert " (" key ") " description "\n")
          (setq option-alist (cons (list key name args)
                                   option-alist))
          (setq key (1+ key))))
      (let ((window-conf (current-window-configuration)))
        (unwind-protect
            (progn
              (with-selected-window (display-buffer buf)
                (goto-char (point-min)))
              (fit-window-to-buffer (get-buffer-window buf))
              (let* ((key (read-key "Refactoring action? "))
                     (entry (cdr (assoc key option-alist))))
                (kill-buffer buf)
                (cons (car entry)       ; name
                      (elpy-refactor-build-arguments (cadr entry)
                                                     pos))))
          (set-window-configuration window-conf))))))

(defun elpy-refactor-build-arguments (args pos)
  "Translate an argument list specification to an argument list.

POS is a vector of three elements, the current offset, the offset
of the beginning of the region, and the offset of the end of the
region.

ARGS is a list of triples, each triple containing the name of an
argument (ignored), the type of the argument, and a possible
prompt string.

Available types:

  offset       - The offset in the buffer, (1- (point))
  start_offset - Offset of the beginning of the region
  end_offset   - Offset of the end of the region
  string       - A free-form string
  filename     - A non-existing file name
  directory    - An existing directory name
  boolean      - A boolean question"
  (mapcar (lambda (arg)
            (let ((type (cadr arg))
                  (prompt (caddr arg)))
              (cond
               ((equal type "offset")
                (aref pos 0))
               ((equal type "start_offset")
                (aref pos 1))
               ((equal type "end_offset")
                (aref pos 2))
               ((equal type "string")
                (read-from-minibuffer prompt))
               ((equal type "filename")
                (expand-file-name
                 (read-file-name prompt)))
               ((equal type "directory")
                (expand-file-name
                 (read-directory-name prompt)))
               ((equal type "boolean")
                (y-or-n-p prompt)))))
          args))

(defun elpy-refactor-create-change-buffer (changes)
  "Show the user a buffer of changes.

The user can review the changes and confirm them with
\\[elpy-refactor-commit]."
  (when (not changes)
    (error "No changes for this refactoring action."))
  (with-current-buffer (get-buffer-create "*Elpy Refactor*")
    (elpy-refactor-mode)
    (setq elpy-refactor-changes changes
          elpy-refactor-window-configuration (current-window-configuration))
    (let ((inhibit-read-only t))
      (erase-buffer)
      (elpy-refactor-insert-changes changes))
    (select-window (display-buffer (current-buffer)))
    (goto-char (point-min))))

(defun elpy-refactor-insert-changes (changes)
  "Format and display the changes described in CHANGES."
  (insert (propertize "Use C-c C-c to apply the following changes."
                      'face 'bold)
          "\n\n")
  (dolist (change changes)
    (let ((action (cdr (assq 'action change))))
      (cond
       ((equal action "change")
        (insert (cdr (assq 'diff change))
                "\n"))
       ((equal action "create")
        (let ((type (cdr (assq 'type change))))
          (if (equal type "file")
              (insert "+++ " (cdr (assq 'file change)) "\n"
                      "Create file " (cdr (assq 'file change)) "\n"
                      "\n")
            (insert "+++ " (cdr (assq 'path change)) "\n"
                    "Create directory " (cdr (assq 'path change)) "\n"
                    "\n"))))
       ((equal action "move")
        (insert "--- " (cdr (assq 'source change)) "\n"
                "+++ " (cdr (assq 'destination change)) "\n"
                "Rename " (cdr (assq 'type change)) "\n"
                "\n"))
       ((equal action "delete")
        (let ((type (cdr (assq 'type change))))
          (if (equal type "file")
              (insert "--- " (cdr (assq 'file change)) "\n"
                      "Delete file " (cdr (assq 'file change)) "\n"
                      "\n")
            (insert "--- " (cdr (assq 'path change)) "\n"
                    "Delete directory " (cdr (assq 'path change)) "\n"
                    "\n"))))))))

(defvar elpy-refactor-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map (kbd "C-c C-c") 'elpy-refactor-commit)
    (define-key map (kbd "q") 'bury-buffer)
    (define-key map (kbd "h") 'describe-mode)
    (define-key map (kbd "?") 'describe-mode)
    map)
  "The key map for `elpy-refactor-mode'.")

(define-derived-mode elpy-refactor-mode diff-mode "Elpy Refactor"
  "Mode to display refactoring actions and ask confirmation from the user.

\\{elpy-refactor-mode-map}"
  :group 'elpy
  (view-mode 1))

(defun elpy-refactor-commit ()
  "Commit the changes in the current buffer."
  (interactive)
  (when (not elpy-refactor-changes)
    (error "No changes to commit."))
  ;; Restore the window configuration as the first thing so that
  ;; changes below are visible to the user. Especially the point
  ;; change in possible buffer changes.
  (set-window-configuration elpy-refactor-window-configuration)
  (dolist (change elpy-refactor-changes)
    (let ((action (cdr (assq 'action change))))
      (cond
       ((equal action "change")
        (with-current-buffer (find-file-noselect (cdr (assq 'file change)))
          ;; This would break for save-excursion as the buffer is
          ;; truncated, so all markets now point to position 1.
          (let ((old-point (point)))
            (undo-boundary)
            (erase-buffer)
            (insert (cdr (assq 'contents change)))
            (undo-boundary)
            (goto-char old-point))))
       ((equal action "create")
        (if (equal (cdr (assq 'type change))
                   "file")
            (find-file-noselect (cdr (assq 'file change)))
          (make-directory (cdr (assq 'path change)))))
       ((equal action "move")
        (let* ((source (cdr (assq 'source change)))
               (dest (cdr (assq 'destination change)))
               (buf (get-file-buffer source)))
          (when buf
            (with-current-buffer buf
              (setq buffer-file-name dest)
              (rename-buffer (file-name-nondirectory dest) t)))
          (rename-file source dest)))
       ((equal action "delete")
        (if (equal (cdr (assq 'type change)) "file")
            (let ((name (cdr (assq 'file change))))
              (when (y-or-n-p (format "Really delete %s? " name))
                (delete-file name t)))
          (let ((name (cdr (assq 'directory change))))
            (when (y-or-n-p (format "Really delete %s? " name))
              (delete-directory name nil t))))))))
  (kill-buffer (current-buffer)))

(defun elpy-refactor-rpc-get-options ()
  "Get a list of refactoring options from the Elpy RPC."
  (if (use-region-p)
      (elpy-rpc "get_refactor_options"
                (list (buffer-file-name)
                      (1- (region-beginning))
                      (1- (region-end))))
    (elpy-rpc "get_refactor_options"
              (list (buffer-file-name)
                    (1- (point))))))

(defun elpy-refactor-rpc-get-changes (method args)
  "Get a list of changes from the Elpy RPC after applying METHOD with ARGS."
  (elpy-rpc "refactor"
            (list (buffer-file-name)
                  method args)))

(provide 'elpy-refactor)
;;; elpy-refactor.el ends here
