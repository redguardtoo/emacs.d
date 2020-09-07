;;; wucuo-flyspell-org-verify.el --- verify typo in org file  -*- lexical-binding: t -*-

;; Copyright (C) 2020 Chen Bin
;;
;; This file is NOT part of GNU Emacs.

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 3, or (at your option)
;; any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program; if not, see <https://www.gnu.org/licenses/>.

;;; Commentary:

;;

;;; Code:

(require 'wucuo-sdk)

(defun wucuo-org-mode-code-snippet-p ()
  "Code snippet embedded in org file?"
  (let* (rlt
         (begin-regexp "^[ \t]*#\\+begin_\\(src\\|html\\|latex\\|example\\)")
         (end-regexp "^[ \t]*#\\+end_\\(src\\|html\\|latex\\|example\\)")
         (case-fold-search t)
         b e)
    (save-excursion
      (if (setq b (re-search-backward begin-regexp nil t))
          (setq e (re-search-forward end-regexp nil t))))
    (if (and b e (< (point) e)) (setq rlt t))
    rlt))

;;;###autoload
(defun wucuo-flyspell-org-verify ()
  "Verify typo in org file."
  (let* ((f (wucuo-sdk-get-font-face (1- (point))))
         (rlt t))
    (cond
     ;; skip checking in below fonts
     ((memq f '(org-verbatim org-code))
      (setq rlt nil))

     ;; skip checking property lines
     ((string-match "^[ \t]+:[A-Z]+:[ \t]+" (wucuo-sdk-current-line))
      (setq rlt nil))

     ;; skipping checking in code snippet
     ;; slow test should be placed at last
     ((wucuo-org-mode-code-snippet-p)
      (setq rlt nil)))
    ;; If rlt is t, it's a typo. If nil, not a typo.
    rlt))

(provide 'wucuo-flyspell-org-verify)
;;; wucuo-flyspell-org-verify.el ends here
