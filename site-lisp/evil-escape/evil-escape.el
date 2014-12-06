;;; evil-escape.el --- Customizable key sequence to escape from insert state and everything else.

;; Copyright (C) 2014 syl20bnr
;;
;; Author: Sylvain Benner <sylvain.benner@gmail.com>
;; Keywords: convenience editing evil
;; Created: 22 Oct 2014
;; Version: 1.6.2
;; Package-Requires: ((emacs "24") (evil "1.0.9") (key-chord "0.6"))
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

;;   - escape from all evil states to normal state
;;   - escape from evil-lisp-state to normal state
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
;;   - hide neotree buffer
;; And more to come !

;; Configuration:
;; --------------

;; The key sequence can be customized with the variable
;; `evil-escape-key-sequence'
;; It must be set before requiring evil-escape.

;; `evil-escape' is not compatible with sequences that start with `h j k or l`
;; so avoid to define a sequence that starts with a navigation key.

;; More information in the readme of the repository:
;; https://github.com/syl20bnr/evil-escape

;;; Code:

(require 'evil)
(require 'key-chord)

(defgroup evil-escape nil
  "Key sequence to escape insert state and everything else."
  :prefix "evil-escape-"
  :group 'evil)

(eval-and-compile
  (defcustom evil-escape-key-sequence (kbd "fd")
    "Two keys sequence to escape from insert state."
    :type 'key-sequence
    :group 'evil-escape))

(defvar evil-escape-motion-state-shadowed-func nil
  "Original function of `evil-motion-state' shadowed by `evil-espace'.
This variable is used to restore the original function bound to the
first key of the escape key sequence when `evil-escape'
mode is disabled.")

(defvar evil-escape-isearch-shadowed-func nil
  "Original function of `isearch-mode-map' shadowed by `evil-escape'.
This variable is used to restore the original function bound to the
first key of the escape key sequence when `evil-escape'
mode is disabled.")

;;;###autoload
(define-minor-mode evil-escape-mode
  "Buffer-local minor mode to escape insert state and everythin else
with a key sequence."
  :lighter (:eval (concat " " evil-escape-key-sequence))
  :group 'evil
  :global t
  (if evil-escape-mode
      (progn
        (key-chord-mode 1)
        (evil-escape--define-keys)
        (message "evil-escape enabled, press \"%s\" to escape from anything."
                 evil-escape-key-sequence))
    (evil-escape--undefine-keys)))

(eval-and-compile
  (defun evil-escape--first-key ()
    "Return the first key string in the key sequence."
    (let* ((first-key (elt evil-escape-key-sequence 0))
           (fkeystr (char-to-string first-key)))
      fkeystr)))

(defmacro evil-escape-define-escape (map command &rest properties)
  "Define an escape in MAP keymap by executing COMMAND.

`:insert BOOL'
     If BOOL is not nil the first character of the escape sequence is inserted
     in the buffer using `:insert-func' if the buffer is not read-only.

`:delete BOOL'
     If BOOL is not nil the first character is deleted using `:delete-func' if
     the escape sequence succeeded.

`:shadowed-map MAP'
     MAP not nil indicates that the first key of the sequence shadows a
     function bound in MAP. This function is looked-up from
     `evil-motion-state-map'.
     Whenever the escape sequence does not succeed and MAP is not nil
     the shadowed function is called.

`:insert-func FUNCTION'
     Specify the insert function to call when inserting the first key.

`:delete-func FUNCTION'
     Specify the delete function to call when deleting the first key."
  (let ((insertp (plist-get properties :insert))
        (deletep (plist-get properties :delete))
        (shadowed-map (plist-get properties :shadowed-map))
        (insert-func (plist-get properties :insert-func))
        (delete-func (plist-get properties :delete-func)))
    `(progn
       (define-key ,map ,(evil-escape--first-key)
         (lambda () (interactive)
           (evil-escape--escape
            ,evil-escape-key-sequence
            ',(if (plist-get properties :shadowed-map)
                  (lookup-key shadowed-map (evil-escape--first-key)))
            ,insertp
            ,deletep
            ',command
            ',insert-func
            ',delete-func))))))

(defun evil-escape--define-keys ()
  "Set the key bindings to escape _everything!_"
  ;; use key-chord whenever it is possible
  ;; evil states
  ;; insert state
  (key-chord-define evil-insert-state-map evil-escape-key-sequence 'evil-normal-state)
  ;; emacs state
  (key-chord-define evil-emacs-state-map evil-escape-key-sequence
                    '(lambda () (interactive)
                       (cond ((string-match "magit" (symbol-name major-mode))
                              (setq unread-command-events (listify-key-sequence "q")))
                             ((eq 'paradox-menu-mode major-mode)
                              (paradox-quit-and-close))
                             ((eq 'gist-list-menu-mode major-mode)
                              (quit-window))
                             (t  evil-normal-state))))
  ;; visual state
  (key-chord-define evil-visual-state-map evil-escape-key-sequence 'evil-exit-visual-state)
  ;; motion state
  (setq evil-escape-motion-state-shadowed-func
        (lookup-key evil-motion-state-map (evil-escape--first-key)))
  (let ((exit-func (lambda () (interactive)
                     (cond ((or (eq 'apropos-mode major-mode)
                                (eq 'help-mode major-mode)
                                (eq 'ert-results-mode major-mode)
                                (eq 'ert-simple-view-mode major-mode))
                            (quit-window))
                           ((eq 'undo-tree-visualizer-mode major-mode)
                            (undo-tree-visualizer-quit))
                           ((eq 'neotree-mode major-mode) (neotree-hide))
                           (t (evil-normal-state))))))
    (eval `(evil-escape-define-escape evil-motion-state-map ,exit-func
                                      :shadowed-map ,evil-motion-state-map)))
  ;; lisp state if installed
  (eval-after-load 'evil-lisp-state
    '(key-chord-define evil-lisp-state-map evil-escape-key-sequence 'evil-normal-state))
  ;; mini-buffer
  (key-chord-define minibuffer-local-map evil-escape-key-sequence 'abort-recursive-edit)
  ;; evil ex command
  (key-chord-define evil-ex-completion-map evil-escape-key-sequence 'abort-recursive-edit)
  ;; key-chord does not work with isearch, use evil-escape implementation
  (setq evil-escape-isearch-shadowed-func
        (lookup-key isearch-mode-map (evil-escape--first-key)))
  (evil-escape-define-escape isearch-mode-map isearch-abort
                             :insert t
                             :delete t
                             :insert-func evil-escape--isearch-insert-func
                             :delete-func isearch-delete-char))

(defun evil-escape--undefine-keys ()
  "Unset the key bindings defined in `evil-escape--define-keys'."
  ;; bulk undefine
  (dolist (map '(evil-insert-state-map
                 evil-emacs-state-map
                 evil-visual-state-map
                 minibuffer-local-map
                 evil-ex-completion-map))
    (key-chord-define (eval map) evil-escape-key-sequence nil))
  ;; lisp state if installed
  (eval-after-load 'evil-lisp-state
    '(key-chord-define evil-lisp-state-map evil-escape-key-sequence nil))
  (let ((first-key (evil-escape--first-key)))
    ;; motion state
    (if evil-escape-motion-state-shadowed-func
        (define-key evil-motion-state-map
          (kbd first-key) evil-escape-motion-state-shadowed-func))
    ;; isearch
    (if evil-escape-isearch-shadowed-func
        (define-key isearch-mode-map
          (kbd first-key) evil-escape-isearch-shadowed-func))))

(defun evil-escape--default-insert-func (key)
  "Insert KEY in current buffer if not read only."
  (let* ((insertp (not buffer-read-only)))
    (insert key)))

(defun evil-escape--isearch-insert-func (key)
  "Insert KEY in current buffer if not read only."
  (isearch-printing-char))

(defun evil-escape--default-delete-func ()
  "Delete char in current buffer if not read only."
  (let* ((insertp (not buffer-read-only)))
    (delete-char -1)))

(defun evil-escape--call-evil-function (func)
  "Call the passed evil function appropriatly."
  (if (eq 'inclusive (evil-get-command-property func :type))
      (setq evil-this-type 'inclusive))
  (call-interactively shadowed-func))

(evil-define-command evil-escape--escape
  (keys shadowed-func insert? delete? callback &optional insert-func delete-func)
  "Execute the passed CALLBACK using KEYS. KEYS is a cons cell of 2 characters.

If the first key insertion shadowed a function then pass the shadowed function
in SHADOWED-FUNC and it will be executed if the key sequence was not
 successfull.

If INSERT? is not nil then the first key pressed is inserted using the function
INSERT-FUNC.

If DELETE? is not nil then the first key is deleted using the function
DELETE-FUNC when calling CALLBACK. "
  :repeat nil
  (if (and shadowed-func (eq 'normal evil-state))
      (evil-escape--call-evil-function shadowed-func)
    (let* ((modified (buffer-modified-p))
           (insertf (if insert-func
                        insert-func 'evil-escape--default-insert-func))
           (deletef (if delete-func
                        delete-func 'evil-escape--default-delete-func))
           (fkey (elt keys 0))
           (fkeystr (char-to-string fkey))
           (skey (elt keys 1)))
      (if insert? (funcall insertf fkey))
      (let* ((evt (read-event nil nil key-chord-two-keys-delay)))
        (cond
         ((null evt)
          (unless (eq 'insert evil-state)
            (if shadowed-func (evil-escape--call-evil-function shadowed-func))))
         ((and (integerp evt)
               (char-equal evt skey))
          ;; remove the f character
          (if delete? (funcall deletef))
          (set-buffer-modified-p modified)
          (funcall callback))
         (t ; otherwise
          (setq unread-command-events
                (append unread-command-events (list evt)))
          (if shadowed-func (evil-escape--call-evil-function shadowed-func)))))
      )))

(provide 'evil-escape)
;;; evil-escape.el ends here
