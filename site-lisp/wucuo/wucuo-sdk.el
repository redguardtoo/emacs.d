;;; wucuo-sdk.el --- SDK for wucuo  -*- lexical-binding: t -*-

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

;;;###autoload
(defun wucuo-sdk-current-line ()
  "Current line."
  (buffer-substring-no-properties (line-beginning-position) (line-end-position)))

;;;###autoload
(defun wucuo-sdk-get-font-face (position)
  "Get font face at POSITION."
  (get-text-property position 'face))

(provide 'wucuo-sdk)
;;; wucuo-sdk.el ends here
