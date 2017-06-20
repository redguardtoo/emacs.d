;;; evil-mark-replace.el --- replace the thing in marked area

;; Copyright (C) 2015 Chen Bin

;; Author: Chen Bin <chenbin.sh@gmail.com>
;; URL: http://github.com/redguardtoo/evil-mark-replace
;; Keywords: mark replace evil
;; Version: 0.0.4
;; Package-Requires: ((evil "1.0.8"))

;; This file is not part of GNU Emacs.

;;; Commentary:

;; See http://github.com/redguardtoo/evil-mark-replace
;;
;; Install:
;;  (require 'evil-mark-replace)
;;
;; Usage:
;;  Example 1, `M-x evilmr-replace-in-defun'
;;  Example 2, `M-x evilmr-replace-in-buffer'
;;  Example 3, Select a region, `M-x evilmr-tag-selected-region'.
;;             Then `M-x evilmr-replace-in-tagged-region'

;; This file is free software (GPLv3 License)

;;; Code:

(require 'evil)

(defvar evilmr-tagged-region-begin nil)
(defvar evilmr-tagged-region-end nil)

;;;###autoload
(defun evilmr-replace (MARK-FN)
  "Mark region with MAKR-FN. Then replace in marked area."
  (let ((old (if (region-active-p)
                 (buffer-substring-no-properties (region-beginning) (region-end))
               (thing-at-point 'symbol)))
        escaped-old)
    (unless old (setq old (read-string "String to be replaced:")) )

    (setq escaped-old (replace-regexp-in-string "\\$" "\\\\$" old))

    ;; quit the active region
    (if (region-active-p) (set-mark nil))

    (funcall MARK-FN)
    (unless (evil-visual-state-p)
      (kill-new old)
      (evil-visual-state))
    (evil-ex (concat "'<,'>s%" escaped-old "%"))))

;;;###autoload
(defun evilmr-show-tagged-region ()
  "Mark and show tagged region"
  (interactive)
  (let (opoint)
    (when (and evilmr-tagged-region-begin
               evilmr-tagged-region-end)
      (goto-char (1+ evilmr-tagged-region-end))
      (push-mark (point) nil t)
      (goto-char evilmr-tagged-region-begin)
      )))

;;;###autoload
(defun evilmr-tag-selected-region ()
  "Tag selected region"
  (interactive)
  (cond
   ((region-active-p)
    (setq evilmr-tagged-region-begin (region-beginning))
    (setq evilmr-tagged-region-end (region-end))
    (set-mark nil)
    (message "Region from %d to %d is tagged"
             evilmr-tagged-region-begin
             evilmr-tagged-region-end))
   (t (message "NO region is tagged"))))

;;;###autoload
(defun evilmr-replace-in-buffer ()
"Mark buffer and replace the thing,
which is either symbol under cursor or the selected text"
  (interactive)
  (evilmr-replace 'mark-whole-buffer))

;;;###autoload
(defun evilmr-replace-in-defun ()
  "Mark defun and replace the thing
  which is either symbol under cursor or the selected text"
  (interactive)
  (evilmr-replace 'mark-defun))

;;;###autoload
(defun evilmr-replace-in-tagged-region ()
"Mark tagged region and replace the thing,
which is either symbol under cursor or the selected text"
  (interactive)
  (evilmr-replace 'evilmr-show-tagged-region))

;;;###autoload
(defun evilmr-version ()
  (interactive)
  (message "0.0.4"))

(provide 'evil-mark-replace)

;;; evil-mark-replace.el ends here
