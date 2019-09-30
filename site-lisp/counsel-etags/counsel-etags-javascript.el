;;; counsel-etags-javascript.el --- rules to filter tags for javascript

;; Copyright (C) 2018, 2019 Chen Bin

;; Author: Chen Bin <chenbin DOT sh AT gmail DOT com>

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 3, or (at your option)
;; any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program; if not, write to the Free Software
;; Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.


;;; Commentary:

;;; Code:

(require 'counsel-etags-sdk)

;;;###autoload
(defun counsel-etags-javascript-collect ()
  "Get CONTEXT before finding tag definition."
  (let* ((context (counsel-etags-sdk-get-context)))
    ;; if current tags is "this.onSelect", only search in current file
    (when (string-match-p "^this\.[0-9a-zA-Z]+"
                          (counsel-etags-sdk-thing-at-point "_."))
      (setq context (plist-put context :local-only t)))
    context))

;;;###autoload
(defun counsel-etags-javascript-predicate (context candidate)
  "Use CONTEXT to test CANDIDATE.  If return nil, the CANDIDATE is excluded."
  (cond
   ((plist-get context :local-only)
    (let* ((src-file (plist-get context :fullpath))
           (def-file (plist-get candidate :fullpath)))
      ;; (message "src-file=%s def-file=%s rlt=%s" src-file def-file (string= src-file def-file))
      (string= src-file def-file)))
   (t
    t)))

(provide 'counsel-etags-javascript)
;;; counsel-etags-javascript.el ends here
