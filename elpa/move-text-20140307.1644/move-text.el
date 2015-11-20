;;; move-text.el --- Move current line or region with M-up or M-down.

;; Filename: move-text.el
;; Description: Move current line or region with M-up or M-down.
;; Author: Jason M <jasonm23@gmail.com>
;; Extracted from basic-toolkit.el by Andy Stewart.
;; Copyright (C) 2009, Andy Stewart, all rights reserved.
;; Keywords: edit
;; Package-Version: 20140307.1644
;; Compatibility: GNU Emacs 23.0.60.1
;; Version: 1.0
;;
;;; This file is NOT part of GNU Emacs

;;; License
;;
;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 3, or (at your option)
;; any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program; see the file COPYING.  If not, write to
;; the Free Software Foundation, Inc., 51 Franklin Street, Fifth
;; Floor, Boston, MA 02110-1301, USA.

;;; Commentary:
;;
;; MoveText is extracted from Basic edit toolkit.
;; It allows you to move the current line using M-up / M-down
;; if a region is marked, it will move the region instead.
;;

;;; Installation:
;;
;; Put move-text.el to your load-path.
;; The load-path is usually ~/elisp/.
;; It's set in your ~/.emacs like this:
;; (add-to-list 'load-path (expand-file-name "~/elisp"))
;;
;; And the following to your ~/.emacs startup file.
;;
;; (require 'move-text)
;; (move-text-default-bindings)
;;

;;; Acknowledgements:
;;
;;  Feature extracted from basid-edit-toolkit.el - by Andy Stewart. (LazyCat)
;;

;;; Code:

(defun move-text-internal (arg)
  (cond
   ((and mark-active transient-mark-mode)
    (if (> (point) (mark))
        (exchange-point-and-mark))
    (let ((column (current-column))
          (text (delete-and-extract-region (point) (mark))))
      (forward-line arg)
      (move-to-column column t)
      (set-mark (point))
      (insert text)
      (exchange-point-and-mark)
      (setq deactivate-mark nil)))
   (t
    (let ((column (current-column)))
      (beginning-of-line)
      (when (or (> arg 0) (not (bobp)))
        (forward-line)
        (when (or (< arg 0) (not (eobp)))
          (transpose-lines arg)
          ;; Account for changes to transpose-lines in Emacs 24.3
          (when (and (eval-when-compile
                       (not (version-list-<
                             (version-to-list emacs-version)
                             '(24 3 50 0))))
                     (< arg 0))
            (forward-line -1)))
        (forward-line -1))
      (move-to-column column t)))))

;;;###autoload
(defun move-text-down (arg)
  "Move region (transient-mark-mode active) or current line
  arg lines down."
  (interactive "*p")
  (move-text-internal arg))

;;;###autoload
(defun move-text-up (arg)
  "Move region (transient-mark-mode active) or current line
  arg lines up."
  (interactive "*p")
  (move-text-internal (- arg)))

;;;###autoload
(defun move-text-default-bindings ()
  "Bind `move-text-up' and `move-text-down' to M-up and M-down."
  (global-set-key [M-up] 'move-text-up)
  (global-set-key [M-down] 'move-text-down))

(provide 'move-text)

;;; move-text.el ends here
