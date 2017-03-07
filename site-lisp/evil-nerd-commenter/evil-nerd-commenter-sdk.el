;;; evil-nerd-commenter-sdk.el --- SDK used by other files

;; Copyright (C) 2017 Chen Bin

;; Author: Chen Bin <chenin DOT sh AT gmail DOT com>

;;; License:

;; This file is not part of GNU Emacs.

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 2, or (at your option)
;; any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program; if not, write to the Free Software
;; Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.

;;; Commentary:
;; SDK used internally

;;; Code:

(defun evilnc--check-fonts (fonts-under-cursor fonts-list)
  (delq nil
        (mapcar #'(lambda (f)
                    ;; learn this trick from flyspell
                    (member f fonts-list))
                fonts-under-cursor)))

(defun evilnc-web-mode-is-comment (&optional pos)
  "Check whether the code at POS is comment.
`web-mode' removes its API, so create our own."
  (unless pos (setq pos (point)))
  (not (null (or (eq (get-text-property pos 'tag-type) 'comment)
                 (eq (get-text-property pos 'block-token) 'comment)
                 (eq (get-text-property pos 'part-token) 'comment)))))

(defun evilnc-is-comment (pos)
  "Check whether the code at POS is comment by comparing font face."
  (let* ((fontfaces (if (> pos 0) (get-text-property pos 'face))))
    (if (not (listp fontfaces))
        (setf fontfaces (list fontfaces)))
    (cond
     ((or (< pos (point-min)) (> pos (point-max)))
      nil)
     ((and (not fontfaces)
           ;; character under cursor is SPACE or TAB
           (member (evilnc-get-char pos) '(32 9)))
      t)
     ((string= major-mode "web-mode")
      (evilnc-web-mode-is-comment pos))
     (t
      (evilnc--check-fonts fontfaces
                           '(font-lock-comment-face
                             font-lock-comment-delimiter-face))))))

(defun evilnc-get-char (pos)
  (save-excursion
    (goto-char pos)
    (following-char)))

(defun evilnc-is-comment-delimiter (pos)
  (let* ((fontfaces (if (> pos 0) (get-text-property pos 'face))))
    (if (not (listp fontfaces))
        (setf fontfaces (list fontfaces)))
    (and fontfaces
         (evilnc--check-fonts fontfaces
                              '(font-lock-comment-delimiter-face)))))

(provide 'evil-nerd-commenter-sdk)
;;; evil-nerd-commenter-sdk.el ends here

