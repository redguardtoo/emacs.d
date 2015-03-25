;;; evil-mark-replace --- replace text in evil way

;; Copyright (C) 2015 Chen Bin

;; Author: Chen Bin <chenbin.sh@gmail.com>
;; URL: http://github.com/redguardtoo/evil-mark-replace
;; Keywords: mark replace evil
;; Version: 0.0.2
;; Package-Requires: ((evil "1.0.8"))

;; This file is not part of GNU Emacs.

;;; Commentary:

;; See http://github.com/redguardtoo/evil-mark-replace
;;
;; Install:
;;  (require 'evil-mark-replace)
;;
;; Example usage:
;;  1. `M-x evil-mark-replace-in-defun'
;;  2. `M-x evil-mark-replace-in-buffer'
;;  3. Select a region, `M-x evil-mark-tag-selected-region'.
;;     Then `M-x evil-mark-replace-in-tagged-region'

;; This file is free software (GPLv3 License)

;;; Code:

(require 'evil)

(defvar evil-mark-tagged-region-begin nil)
(defvar evil-mark-tagged-region-end nil)

;;;###autoload
(defun evil-mark-replace-string (MARK-FN)
  "Mark region with MAKR-FN. Then replace in marked area."
  (let ((old (if (region-active-p)
                 (buffer-substring-no-properties (region-beginning) (region-end))
               (thing-at-point 'symbol)))
        escaped-old)

    (setq escaped-old (replace-regexp-in-string "\\$" "\\\\$" old))

    ;; quit the active region
    (if (region-active-p) (set-mark nil))

    (funcall MARK-FN)
    (unless (evil-visual-state-p)
      (kill-new old)
      (evil-visual-state))
    (evil-ex (concat "'<,'>s/\\<\\(" escaped-old "\\)\\>/"))))

;;;###autoload
(defun evil-mark-show-tagged-region ()
  "Mark and show tagged region"
  (interactive)
  (let (opoint)
    (when (and evil-mark-tagged-region-begin
               evil-mark-tagged-region-end)
      (goto-char (1+ evil-mark-tagged-region-end))
      (push-mark (point) nil t)
      (goto-char evil-mark-tagged-region-begin)
      )))

;;;###autoload
(defun evil-mark-tag-selected-region ()
  "Tag selected region"
  (interactive)
  (cond
   ((region-active-p)
    (setq evil-mark-tagged-region-begin (region-beginning))
    (setq evil-mark-tagged-region-end (region-end))
    (set-mark nil)
    (message "Region from %d to %d is tagged"
             evil-mark-tagged-region-begin
             evil-mark-tagged-region-end))
   (t (message "NO region is tagged"))))

;;;###autoload
(defun evil-mark-replace-in-buffer ()
"Mark buffer and replace the thing,
which is either symbol under cursor or the selected text"
  (interactive)
  (evil-mark-replace-string 'mark-whole-buffer))

;;;###autoload
(defun evil-mark-replace-in-defun ()
  "Mark defun and replace the thing
  which is either symbol under cursor or the selected text"
  (interactive)
  (evil-mark-replace-string 'mark-defun))

;;;###autoload
(defun evil-mark-replace-in-tagged-region ()
"Mark tagged region and replace the thing,
which is either symbol under cursor or the selected text"
  (interactive)
  (evil-mark-replace-string 'evil-mark-show-tagged-region))

;;;###autoload
(defun evil-mark-version ()
  (interactive)
  (message "0.0.2"))

(provide 'evil-mark-replace)

;;; evil-mark-replace.el ends here
