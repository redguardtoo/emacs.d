;;; evil-escape.el --- Escape from anything with a customizable key sequence

;; Copyright (C) 2014-2015 syl20bnr
;;
;; Author: Sylvain Benner <sylvain.benner@gmail.com>
;; Keywords: convenience editing evil
;; Created: 22 Oct 2014
;; Version: 3.07
;; Package-Requires: ((emacs "24") (evil "1.0.9"))
;; URL: https://github.com/syl20bnr/evil-escape

;; This file is not part of GNU Emacs.

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:

;; Press `fd` quickly to:
;; ----------------------

;;   - escape from all stock evil states to normal state
;;   - escape from evil-lisp-state to normal state
;;   - escape from evil-iedit-state to normal state
;;   - abort evil ex command
;;   - quit minibuffer
;;   - abort isearch
;;   - quit magit buffers
;;   - quit help buffers
;;   - quit apropos buffers
;;   - quit ert buffers
;;   - quit undo-tree buffer
;;   - quit paradox
;;   - quit gist-list menu
;;   - quit helm-ag-edit
;;   - hide neotree buffer
;; And more to come !

;; Configuration:
;; --------------

;; The key sequence can be customized with the variable
;; `evil-escape-key-sequence'.

;; The delay between the two key presses can be customized with
;; the variable `evil-escape-delay'. Default is `0.1'.

;; The key sequence can be entered in any order by setting
;; the variable `evil-escape-unordered-key-sequence' to non nil.

;; A major mode can be excluded by adding it to the list
;; `evil-escape-excluded-major-modes'.

;; An inclusive list of major modes can defined with the variable
;; `evil-escape-enable-only-for-major-modes'. When this list is
;; non-nil then evil-escape is enabled only for the major-modes
;; in the list.

;; It is possible to bind `evil-escape' function directly, for
;; instance to execute evil-escape with `C-c C-g':

;; (global-set-key (kbd "C-c C-g") 'evil-escape)

;; More information in the readme of the repository:
;; https://github.com/syl20bnr/evil-escape

;;; Code:

(require 'evil)

(defgroup evil-escape nil
  "Key sequence to escape insert state and everything else."
  :prefix "evil-escape-"
  :group 'evil)

(defcustom evil-escape-key-sequence (kbd "fd")
  "Two keys sequence to escape from insert state."
  :type 'key-sequence
  :group 'evil-escape)

(defcustom evil-escape-delay 0.1
  "Max time delay between two key presses."
  :type 'number
  :group 'evil-escape)

(defcustom evil-escape-unordered-key-sequence nil
  "If non-nil then the key sequence can also be entered with the second
key first."
  :type 'boolean
  :group 'evil-escape)

(defcustom evil-escape-excluded-major-modes nil
  "Excluded major modes where escape sequences has no effect."
  :type 'sexp
  :group 'evil-escape)

(defcustom evil-escape-enable-only-for-major-modes nil
  "List of major modes where evil-escape is enabled."
  :type 'sexp
  :group 'evil-escape)

;;;###autoload
(define-minor-mode evil-escape-mode
  "Buffer-local minor mode to escape insert state and everythin else
with a key sequence."
  :lighter (:eval (concat " " evil-escape-key-sequence))
  :group 'evil
  :global t
  (if evil-escape-mode
      (add-hook 'pre-command-hook 'evil-escape-pre-command-hook)
    (remove-hook 'pre-command-hook 'evil-escape-pre-command-hook)))

(defun evil-escape ()
  "Escape from everything... well almost everything."
  (interactive)
  (pcase evil-state
    (`normal (evil-escape--escape-normal-state))
    (`motion (evil-escape--escape-motion-state))
    (`insert (evil-normal-state))
    (`emacs (evil-escape--escape-emacs-state))
    (`evilified (evil-escape--escape-emacs-state))
    (`visual (evil-exit-visual-state))
    (`replace (evil-normal-state))
    (`lisp (evil-normal-state))
    (`iedit (evil-iedit-state/quit-iedit-mode))
    (`iedit-insert (evil-iedit-state/quit-iedit-mode))
    (_ (evil-escape--escape-normal-state))))

(defun evil-escape-pre-command-hook ()
  "evil-escape pre-command hook."
  (when (evil-escape-p)
    (let ((modified (buffer-modified-p))
          (inserted (evil-escape--insert))
          (fkey (elt evil-escape-key-sequence 0))
          (skey (elt evil-escape-key-sequence 1))
          (evt (read-event nil nil evil-escape-delay)))
      (when inserted (evil-escape--delete))
      (set-buffer-modified-p modified)
      (cond
       ((and (integerp evt)
             (or (char-equal evt skey)
                 (and evil-escape-unordered-key-sequence
                      (char-equal evt fkey))))
        (evil-escape)
        (setq this-command 'ignore))
       ((null evt))
       (t (setq unread-command-events
                (append unread-command-events (list evt))))))))

(defun evil-escape-p ()
  "Return non-nil if evil-escape can run."
  (and (or (window-minibuffer-p)
           (bound-and-true-p isearch-mode)
           (and (fboundp 'helm-alive-p) (helm-alive-p))
           (not (eq evil-state 'normal)))
       (not (memq major-mode evil-escape-excluded-major-modes))
       (or (not evil-escape-enable-only-for-major-modes)
           (memq major-mode evil-escape-enable-only-for-major-modes))
       (or (equal (this-command-keys) (evil-escape--first-key))
           (and evil-escape-unordered-key-sequence
                (equal (this-command-keys) (evil-escape--second-key))))))

(defun evil-escape--escape-normal-state ()
  "Escape from normal state."
  (cond
   ((and (fboundp 'helm-alive-p) (helm-alive-p))
    (abort-recursive-edit))
   ((bound-and-true-p isearch-mode) (isearch-abort))
   ((window-minibuffer-p) (abort-recursive-edit))))

(defun evil-escape--escape-motion-state ()
  "Escape from motion state."
  (cond
   ((or (eq 'apropos-mode major-mode)
        (eq 'help-mode major-mode)
        (eq 'ert-results-mode major-mode)
        (eq 'ert-simple-view-mode major-mode))
    (quit-window))
   ((eq 'undo-tree-visualizer-mode major-mode)
    (undo-tree-visualizer-quit))
   ((and (fboundp 'helm-ag--edit-abort)
         (string-equal "*helm-ag-edit*" (buffer-name)))
    (call-interactively 'helm-ag--edit-abort))
   ((eq 'neotree-mode major-mode) (neotree-hide))
   (t (evil-normal-state))))

(defun evil-escape--escape-emacs-state ()
  "Escape from emacs state."
  (cond ((string-match "magit" (symbol-name major-mode))
         (evil-escape--escape-with-q))
        ((eq 'paradox-menu-mode major-mode)
         (evil-escape--escape-with-q))
        ((eq 'gist-list-menu-mode major-mode)
         (quit-window))
        (t (evil-normal-state))))

(defun evil-escape--first-key ()
  "Return the first key string in the key sequence."
  (let* ((first-key (elt evil-escape-key-sequence 0))
         (fkeystr (char-to-string first-key)))
    fkeystr))

(defun evil-escape--second-key ()
  "Return the second key string in the key sequence."
  (let* ((sec-key (elt evil-escape-key-sequence 1))
         (fkeystr (char-to-string sec-key)))
    fkeystr))

(defun evil-escape--insert-func ()
  "Default insert function."
  (when (not buffer-read-only) (self-insert-command 1)))

(defun evil-escape--delete-func ()
  "Delete char in current buffer if not read only."
  (when (not buffer-read-only) (delete-char -1)))

(defun evil-escape--insert ()
  "Insert the first key of the sequence."
  (pcase evil-state
    (`insert (pcase major-mode
               (`term-mode (call-interactively 'term-send-raw))
               (_ (cond
                   ((bound-and-true-p isearch-mode) (isearch-printing-char))
                   (t (evil-escape--insert-func))))) t)
    (`normal
     (when (window-minibuffer-p) (evil-escape--insert-func) t))
    (`iedit-insert (evil-escape--insert-func) t)))

(defun evil-escape--delete ()
  "Revert the insertion of the first key of the sequence."
  (pcase evil-state
    (`insert (pcase major-mode
               (`term-mode (call-interactively 'term-send-backspace))
               (`deft-mode (call-interactively 'deft-filter-increment))
               (_ (cond
                   ((bound-and-true-p isearch-mode) (isearch-delete-char))
                   (t (evil-escape--delete-func))))))
    (`normal
     (when (minibuffer-window-active-p (evil-escape--delete-func))))
    (`iedit-insert (evil-escape--delete-func))))

(defun evil-escape--escape-with-q ()
  "Send `q' key press event to exit from a buffer."
  (setq unread-command-events (listify-key-sequence "q")))

(provide 'evil-escape)

;;; evil-escape.el ends here
