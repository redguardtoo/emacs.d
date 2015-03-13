;;; evil-mark-replace --- replace text in evil way

;; Copyright (C) 2015 Chen Bin

;; Author: Chen Bin <chenbin.sh@gmail.com>
;; URL: http://github.com/redguardtoo/evil-mark-replace
;; Keywords: mark replace evil
;; Version: 0.0.1

;; This file is not part of GNU Emacs.

;; Usage:

;; See http://github.com/redguardtoo/evil-mark-replace

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
   (t
    (message "NO region is tagged"))))

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
(defun evil-mark-replace-in-region (beg end)
  "Mark in specified region and replace the thing"
  (setq evil-mark-tagged-region-begin beg)
  (setq evil-mark-tagged-region-end end)
  (evil-mark-replace-string 'evil-mark-show-tagged-region))

(evil-define-operator evil-mark-replace-in-text-object-operator (beg end type register yank-handler)
"Mark text object and replace the thing
which is either symbol under cursor or the selected text"
  (interactive "<R><x><y>")
  (evil-apply-on-block #'evil-mark-replace-in-region beg end nil))

;;;###autoload
(defun evil-mark-version ()
  (interactive)
  (message "0.0.1"))

(provide 'evil-mark-replace)

;;; evil-mark-replace.el ends here
