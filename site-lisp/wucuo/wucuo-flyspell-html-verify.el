;;; wucuo-flyspell-html-verify.el --- verify typo in html or xml file -*- lexical-binding: t -*-

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

;;; Code:

(require 'wucuo-sdk)

;;;###autoload
(defun wucuo-flyspell-html-verify ()
  "Verify typo in html and xml file."
  (let* ((f (wucuo-sdk-get-font-face (1- (point))))
         ;; most font faces should be skipped
         rlt)
    (cond
     ;; Check the words whose font face is NOT in below *blacklist*
     ((not (memq f '(web-mode-html-attr-value-face
                     web-mode-html-tag-face
                     web-mode-html-attr-name-face
                     nxml-attribute-local-name
                     nxml-element-local-name
                     web-mode-constant-face
                     web-mode-doctype-face
                     web-mode-keyword-face
                     web-mode-comment-face ;; focus on get html label right
                     web-mode-function-name-face
                     web-mode-variable-name-face
                     web-mode-css-property-name-face
                     web-mode-css-selector-face
                     web-mode-css-color-face
                     web-mode-type-face
                     web-mode-block-control-face)))
      (setq rlt t))

     ;; check attribute value under certain conditions
     ((memq f '(web-mode-html-attr-value-face))
      (save-excursion
        (search-backward-regexp "=['\"]" (line-beginning-position) t)
        (backward-char)
        (setq rlt (string-match "^\\(value\\|class\\|ng[A-Za-z0-9-]*\\)$"
                                (or (thing-at-point 'symbol) ""))))))
    ;; If rlt is t, it's a typo. If nil, not a typo.
    rlt))

(provide 'wucuo-flyspell-html-verify)
;;; wucuo-flyspell-html-verify.el ends here
