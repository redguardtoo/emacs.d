;;; evil-mc.el --- Multiple cursors for evil-mode

;; Copyright © 2015 Gabriel Adomnicai <gabesoft@gmail.com>

;; Author: Gabriel Adomnicai <gabesoft@gmail.com>
;; Maintainer: Gabriel Adomnicai <gabesoft@gmail.com>
;; Version: 0.0.1
;; Keywords: evil editing multiple-cursors vim evil-multiple-cursors evil-mc evil-mc
;; Homepage: https://github.com/gabesoft/evil-mc
;; Package-Requires: ((emacs "24.3") (evil "1.2.5") (cl-lib "0.5"))
;;
;; This file is NOT part of GNU Emacs.

;;; Commentary:

;; This library provides multiple cursors functionality for evil-mode
;;
;; Install:
;;
;; (require 'evil-mc)
;;
;;
;; Usage:
;;
;; (evil-mc-mode 1)        ; enable for a single buffer
;;
;; (global-evil-mc-mode 1) ; enable for all buffers
;;
;;
;; See the README for more details

;;; Code:

(require 'evil)

(require 'evil-mc-common)
(require 'evil-mc-vars)
(require 'evil-mc-undo)
(require 'evil-mc-cursor-state)
(require 'evil-mc-cursor-make)
(require 'evil-mc-command-record)
(require 'evil-mc-command-execute)
(require 'evil-mc-region)

(defcustom evil-mc-mode-line
  `(:eval (if (> (evil-mc-get-cursor-count) 1)
              (format ,(propertize " %s:%d" 'face 'cursor)
                      evil-mc-mode-line-prefix
                      (evil-mc-get-cursor-count))
            (format ,(propertize " %s") evil-mc-mode-line-prefix)))
  "Cursors indicator in the mode line."
  :group 'evil-mc)

(put 'evil-mc-mode-line 'risky-local-variable t)

(defvar evil-mc-key-map
  (let ((map (make-sparse-keymap))
        (keys '(("grm" . evil-mc-make-all-cursors)
                ("gru" . evil-mc-undo-all-cursors)
                ("grs" . evil-mc-pause-cursors)
                ("grr" . evil-mc-resume-cursors)
                ("grf" . evil-mc-make-and-goto-first-cursor)
                ("grl" . evil-mc-make-and-goto-last-cursor)
                ("grh" . evil-mc-make-cursor-here)
                ("M-n" . evil-mc-make-and-goto-next-cursor)
                ("grN" . evil-mc-skip-and-goto-next-cursor)
                ("M-p" . evil-mc-make-and-goto-prev-cursor)
                ("grP" . evil-mc-skip-and-goto-prev-cursor)
                ("C-n" . evil-mc-make-and-goto-next-match)
                ("grn" . evil-mc-skip-and-goto-next-match)
                ("C-t" . evil-mc-skip-and-goto-next-match)
                ("C-p" . evil-mc-make-and-goto-prev-match)
                ("grp" . evil-mc-skip-and-goto-prev-match))))
    (dolist (key-data keys)
      (evil-define-key 'normal map (kbd (car key-data)) (cdr key-data))
      (evil-define-key 'visual map (kbd (car key-data)) (cdr key-data)))
    map))

;;;###autoload
(define-minor-mode evil-mc-mode
  "Toggle evil multiple cursors in a single buffer."
  :group 'evil-mc
  :init-value nil
  :keymap evil-mc-key-map
  :lighter evil-mc-mode-line
  (cond (evil-mc-mode
         (evil-mc-define-vars)
         (evil-mc-initialize-vars)
         (evil-mc-initialize-hooks))
        (t
         (evil-mc-teardown-hooks)))
  (evil-normalize-keymaps))

(put 'evil-mc-mode 'permanent-local t)

;;;###autoload
(define-globalized-minor-mode global-evil-mc-mode
  evil-mc-mode evil-mc-initialize)

;;;###autoload
(defun evil-mc-initialize ()
  "Enable `evil-mc-mode' in the current buffer."
  (evil-mc-mode 1))

;;;###autoload
(defun turn-on-evil-mc-mode ()
  "Turn on evil-mc mode in the current buffer."
  (interactive)
  (evil-mc-mode 1))

;;;###autoload
(defun turn-off-evil-mc-mode ()
  "Turn off evil-mc mode in the current buffer."
  (interactive)
  (evil-mc-mode -1))

(defun evil-mc-define-vars ()
  "Define vars that can be overridden before enabling `evil-mc-mode'."

  (defvar evil-mc-mode-line-prefix "emc"
    "The string used in the mode line to identify `evil-mc-mode'.")

  (defvar evil-mc-incompatible-minor-modes
    '(flyspell-mode flycheck-mode aggressive-indent-mode yas-minor-mode)
    "Minor modes that are incompatible with `evil-mc-mode'.")

  (defvar evil-mc-custom-known-commands nil
    "Custom command handlers. The entries here should have
the same form as those in `evil-mc-known-commands'.
This variable can be used to override default command handlers
implementations."))

(defun evil-mc-initialize-vars ()
  "Initialize all variables used by `evil-mc'."
  (evil-mc-clear-pattern)
  (evil-mc-clear-command)
  (evil-mc-clear-executing-command)
  (evil-mc-clear-recording-command)
  (evil-mc-clear-executing-debug)
  (evil-mc-clear-recording-debug)
  (evil-mc-clear-cursor-list)
  (evil-mc-resume-cursors))

(defun evil-mc-pause-incompatible-modes ()
  "Temporarily disable incompatible minor modes."
  (dolist (mode evil-mc-incompatible-minor-modes)
    (when (and (boundp mode) (eval mode))
      (push mode evil-mc-paused-modes)
      (funcall mode -1))))

(defun evil-mc-resume-incompatible-modes ()
  "Re-enable incompatible minor modes."
  (dolist (mode evil-mc-paused-modes) (funcall mode 1))
  (evil-mc-clear-paused-modes))

(defun evil-mc-initialize-hooks ()
  "Initialize all hooks used by `evil-mc'."
  (add-hook 'evil-mc-before-cursors-created 'evil-mc-pause-incompatible-modes t t)
  (add-hook 'evil-mc-before-cursors-created 'evil-mc-initialize-active-state t t)
  (add-hook 'evil-mc-after-cursors-deleted 'evil-mc-teardown-active-state t t)
  (add-hook 'evil-mc-after-cursors-deleted 'evil-mc-resume-incompatible-modes t t))

(defun evil-mc-teardown-hooks ()
  "Teardown all hooks used by `evil-mc'."
  (remove-hook 'evil-mc-before-cursors-created 'evil-mc-pause-incompatible-modes t)
  (remove-hook 'evil-mc-before-cursors-created 'evil-mc-initialize-active-state t)
  (remove-hook 'evil-mc-after-cursors-deleted 'evil-mc-teardown-active-state t)
  (remove-hook 'evil-mc-after-cursors-deleted 'evil-mc-resume-incompatible-modes t))

(defun evil-mc-initialize-active-state ()
  "Initialize all variables and hooks used while there are active cursors."
  (evil-mc-clear-command)
  (evil-mc-clear-executing-command)
  (evil-mc-clear-recording-command)
  (add-hook 'pre-command-hook 'evil-mc-begin-command-save nil t)
  (add-hook 'post-command-hook 'evil-mc-finish-command-save t t)
  (add-hook 'post-command-hook 'evil-mc-execute-for-all t t)

  (defadvice evil-repeat-keystrokes (before evil-mc-repeat-keystrokes (flag) activate)
    (evil-mc-save-keys-motion flag))
  (defadvice evil-repeat-motion (before evil-mc-repeat-motion (flag) activate)
    (evil-mc-save-keys-operator flag)))

(defun evil-mc-teardown-active-state ()
  "Teardown all variables and hooks used while there are active cursors."
  (remove-hook 'pre-command-hook 'evil-mc-begin-command-save t)
  (remove-hook 'post-command-hook 'evil-mc-finish-command-save t)
  (remove-hook 'post-command-hook 'evil-mc-execute-for-all t)

  (ad-remove-advice 'evil-repeat-keystrokes 'before 'evil-mc-repeat-keystrokes)
  (ad-remove-advice 'evil-repeat-motion 'before 'evil-mc-repeat-motion))

(provide 'evil-mc)

;;; evil-mc.el ends here
