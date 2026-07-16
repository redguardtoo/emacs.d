;;; evil-mark-replace.el --- replace the thing in buffer and defun -*- lexical-binding: t; -*-

;; Copyright (C) 2015-2026 Chen Bin

;; Author: Chen Bin
;; URL: http://github.com/redguardtoo/evil-mark-replace
;; Keywords: convenience
;; Version: 0.0.7
;; Package-Requires: ((evil "1.15.0"))

;; This file is not part of GNU Emacs.

;;; Commentary:

;; Install:
;;  (require 'evil-mark-replace)
;;
;; Usage:
;;  - "M-x evilmr-replace-in-defun"
;;  - "M-x evilmr-replace-in-buffer"
;;

;; This file is free software (GPLv3 License)

;;; Code:

(require 'evil nil t)

(defvar evilmr-group-keyword-p nil
  "If it's t, keyword in ex is grouped like \\(keyword\\).")

;;;###autoload
(defun evilmr-toggle-group-keyword-p ()
  "Toggle `evilmr-group-keyword-p'."
  (interactive)
  (setq evilmr-group-keyword-p (not evilmr-group-keyword-p))
  (message "Now evilmr-group-keyword-p=%s" evilmr-group-keyword-p))

;;;###autoload
(defun evilmr-replace (&optional narrow-fn)
  "Replace in narrowed region if NARROW-FN is not nil.  Or replace in buffer."
  (let* ((old (if (region-active-p)
                  (buffer-substring-no-properties (region-beginning) (region-end))
                (thing-at-point 'symbol)))
         escaped-old)
    (unless old (setq old (read-string "String to be replaced:")) )

    (setq escaped-old (regexp-quote old))

    (when (functionp narrow-fn)
      (funcall narrow-fn))

    ;; quit the active region
    (if (region-active-p) (deactivate-mark))

    ;; In emacs, buffer can be narrowed
    (evil-ex (concat "%s/"
                     (if evilmr-group-keyword-p "\\(")
                     escaped-old
                     (if evilmr-group-keyword-p "\\)")
                     (if evilmr-group-keyword-p "/\\1" "/")))))

;;;###autoload
(defun evilmr-replace-in-buffer ()
  "Replace in buffer.."
  (interactive)
  (evilmr-replace))

;;;###autoload
(defun evilmr-replace-in-defun ()
  "Narrow to defun and replace in narrowed buffer."
  (interactive)
  (evilmr-replace #'narrow-to-defun))

;;;###autoload
(defun evilmr-version ()
  "Print current version."
  (interactive)
  (message "0.0.7"))

(provide 'evil-mark-replace)
;;; evil-mark-replace.el ends here
