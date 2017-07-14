;;; evil-iedit-state.el --- Evil states to interface iedit mode.

;; Copyright (C) 2014 syl20bnr
;;
;; Author: Sylvain Benner <sylvain.benner@gmail.com>
;; Keywords: convenience editing evil iedit mnemonic
;; Created: 12 Dec 2014
;; Version: 1.2
;; Package-Requires: ((evil "1.0.9") (iedit "0.97"))
;; URL: https://github.com/syl20bnr/evil-iedit-state

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

;; Adds two new Evil states `iedit' and `iedit insert' with expand-region
;; integration.

;; For more info visit: https://github.com/syl20bnr/evil-iedit-state

(require 'evil)
(require 'iedit)

(defvar evil-iedit-state-default-state 'normal
  "The state to activate when exiting iedit state")

(evil-define-state iedit
  "`iedit state' interfacing iedit mode."
  :tag " <E> "
  :enable (normal)
  :cursor box
  :message "-- IEDIT --"
  ;; force iedit mode
  (if (evil-replace-state-p) (call-interactively 'iedit-mode)))

(evil-define-state iedit-insert
  "Replace insert state in `iedit state'."
  :tag " <Ei> "
  :enable (insert)
  :cursor (bar . 2)
  :message "-- IEDIT-INSERT --"
  :input-method t)

(defun evil-iedit-state/iedit-mode (&optional arg)
  "Start `iedit-mode'."
  (interactive "P")
  (if (fboundp 'ahs-clear) (ahs-clear))
  (iedit-mode arg)
  (evil-iedit-state))

(defun evil-iedit-state/quit-iedit-mode ()
  "Quit iedit-mode and return set state `evil-iedit-state-default-state'."
  (interactive)
  (iedit-done)
  (funcall (intern (format "evil-%S-state" evil-iedit-state-default-state))))

(defmacro evil-iedit-state||swith-to-insert-state-after-command
    (command &optional interactive)
  "Call COMMAND and switch to iedit-insert state.
If INTERACTIVE is non-nil then COMMAND is called interactively."
  `(progn
     (if ,interactive
         (call-interactively ',command)
       (funcall ',command))
     ;; required to correctly update the cursors
     (evil-iedit-state)
     (evil-iedit-insert-state)))

(defun evil-iedit-state//goto-overlay-start ()
  "Return the position of the start of the current overlay."
  (let ((overlay (iedit-find-current-occurrence-overlay)))
    (if overlay
        (goto-char (overlay-start overlay))
      (call-interactively 'evil-digit-argument-or-evil-beginning-of-line))))

(defun evil-iedit-state//goto-overlay-end ()
  "Return the position of the end of the current overlay."
  (let ((overlay (iedit-find-current-occurrence-overlay)))
    (if overlay
        (goto-char (overlay-end overlay))
      (call-interactively 'evil-end-of-line))))

(defun evil-iedit-state/evil-beginning-of-line (count)
  "Go to the beginning of the current overlay."
  (interactive "p")
  (evil-iedit-state//goto-overlay-start))

(defun evil-iedit-state/evil-end-of-line ()
  "Go to the beginning of the current overlay."
  (interactive)
  (evil-iedit-state//goto-overlay-end))

(defun evil-iedit-state/evil-append-line ()
  "Put the point at then end of current overlay and switch to
`iedit-insert state'."
  (interactive)
  (evil-iedit-state||swith-to-insert-state-after-command
   evil-iedit-state//goto-overlay-end))

(defun evil-iedit-state/evil-insert-line ()
  "Put the point at then end of current overlay and switch to
`iedit-insert state'."
  (interactive)
  (evil-iedit-state||swith-to-insert-state-after-command
   evil-iedit-state//goto-overlay-start))

(defun evil-iedit-state/substitute ()
  "Wipe all the occurrences and switch in `iedit-insert state'"
  (interactive)
  (iedit-delete-occurrences)
  (evil-iedit-insert-state))

(defun evil-iedit-state/evil-change ()
  "Wipe all the occurrences and switch in `iedit-insert state'"
  (interactive)
  (evil-iedit-state||swith-to-insert-state-after-command evil-change t))

(defun evil-iedit-state/evil-append ()
  "Append and switch to `iedit-insert state'"
  (interactive)
  (evil-iedit-state||swith-to-insert-state-after-command evil-append t))

(defun evil-iedit-state/evil-open-below ()
  "Insert new line below and switch to `iedit-insert state'"
  (interactive)
  (evil-iedit-state||swith-to-insert-state-after-command evil-open-below t))

(defun evil-iedit-state/evil-open-above ()
  "Insert new line above and switch to `iedit-insert state'"
  (interactive)
  (evil-iedit-state||swith-to-insert-state-after-command evil-open-above t))

(defun evil-iedit-state/evil-substitute ()
  "Append and switch to `iedit-insert state'"
  (interactive)
  (evil-iedit-state||swith-to-insert-state-after-command evil-substitute t))

(defun evil-iedit-state/paste-replace (count)
  "Replace the selection with the yanked text."
  (interactive "P")
  (iedit-delete-occurrences)
  (evil-paste-before count))

;; expand-region integration, add an "e" command
;;;###autoload
(eval-after-load 'expand-region
  '(progn
     (defun evil-iedit-state/iedit-mode-from-expand-region (&optional arg)
       "Start `iedit-mode'."
       (interactive "P")
       (evil-iedit-state/iedit-mode arg)
       ;; force expand-region temporary overlay map exit
       (setq overriding-terminal-local-map nil))

     (defadvice er/prepare-for-more-expansions-internal
         (around iedit/prepare-for-more-expansions-internal activate)
       ad-do-it
       (let ((default-msg (car ad-return-value))
             (default-bindings (cdr ad-return-value)))
         (setq ad-return-value
               (cons (concat default-msg ", e to edit")
                     (add-to-list 'default-bindings
                                  '("e" evil-iedit-state/iedit-mode-from-expand-region))))))))

;; redefine iedit-done to prevent iedit from putting the occurrence on the
;; kill-ring for no useful reason.
(defun iedit-done ()
  "Exit Iedit mode.
Save the current occurrence string locally and globally.  Save
the initial string globally."
  (when iedit-buffering
      (iedit-stop-buffering))
  (setq iedit-last-occurrence-local (iedit-current-occurrence-string))
  (setq iedit-last-occurrence-global iedit-last-occurrence-local)
  (setq iedit-last-initial-string-global iedit-initial-string-local)
  ;; this is the hack
  ;; (if iedit-last-occurrence-local
  ;; (kill-new iedit-last-occurrence-local)) ; Make occurrence the latest kill in the kill ring.
  (setq iedit-num-lines-to-expand-up 0)
  (setq iedit-num-lines-to-expand-down 0)
  (iedit-cleanup)
  (setq iedit-initial-string-local nil)
  (setq iedit-mode nil)
  (force-mode-line-update)
  (remove-hook 'kbd-macro-termination-hook 'iedit-done t)
  (remove-hook 'change-major-mode-hook 'iedit-done t)
  (remove-hook 'iedit-aborting-hook 'iedit-done t)
  (run-hooks 'iedit-mode-end-hook))

(define-key evil-iedit-state-map "#"   'iedit-number-occurrences)
(define-key evil-iedit-state-map "$"   'evil-iedit-state/evil-end-of-line)
(evil-redirect-digit-argument evil-iedit-state-map "0" 'evil-iedit-state/evil-beginning-of-line)
(define-key evil-iedit-state-map "a"   'evil-iedit-state/evil-append)
(define-key evil-iedit-state-map "A"   'evil-iedit-state/evil-append-line)
(define-key evil-iedit-state-map "c"   'evil-iedit-state/evil-change)
(define-key evil-iedit-state-map "D"   'iedit-delete-occurrences)
(define-key evil-iedit-state-map "F"   'iedit-restrict-function)
(define-key evil-iedit-state-map "gg"  'iedit-goto-first-occurrence)
(define-key evil-iedit-state-map "G"   'iedit-goto-last-occurrence)
(define-key evil-iedit-state-map "i"   'evil-iedit-insert-state)
(define-key evil-iedit-state-map "I"   'evil-iedit-state/evil-insert-line)
(define-key evil-iedit-state-map "J"   'iedit-expand-down-a-line)
(define-key evil-iedit-state-map "K"   'iedit-expand-up-a-line)
(define-key evil-iedit-state-map "L"   'iedit-restrict-current-line)
(define-key evil-iedit-state-map "n"   'iedit-next-occurrence)
(define-key evil-iedit-state-map "N"   'iedit-prev-occurrence)
(define-key evil-iedit-state-map "o"   'evil-iedit-state/evil-open-below)
(define-key evil-iedit-state-map "O"   'evil-iedit-state/evil-open-above)
(define-key evil-iedit-state-map "p"   'evil-iedit-state/paste-replace)
(define-key evil-iedit-state-map "s"   'evil-iedit-state/evil-substitute)
(define-key evil-iedit-state-map "S"   'evil-iedit-state/substitute)
(define-key evil-iedit-state-map "V"   'iedit-toggle-unmatched-lines-visible)
(define-key evil-iedit-state-map "U"   'iedit-upcase-occurrences)
(define-key evil-iedit-state-map (kbd "C-U") 'iedit-downcase-occurrences)
(define-key evil-iedit-state-map (kbd "C-g")'evil-iedit-state/quit-iedit-mode)
(define-key evil-iedit-state-map (kbd "TAB") 'iedit-toggle-selection)
(define-key evil-iedit-state-map [backspace] 'iedit-blank-occurrences)
(define-key evil-iedit-state-map [escape]    'evil-iedit-state/quit-iedit-mode)

(define-key evil-iedit-insert-state-map (kbd "C-g") 'evil-iedit-state/quit-iedit-mode)
(define-key evil-iedit-insert-state-map [escape]    'evil-iedit-state)

;; unbound iedit commands:
;; toggle buffering
;; toggle case sensitive

(provide 'evil-iedit-state)

;;; evil-iedit-state.el ends here
