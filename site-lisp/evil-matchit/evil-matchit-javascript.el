;;; evil-matchit-javascript.el --- simple match plugin of evil-matchit

;; Copyright (C) 2014-2017 Chen Bin <chenbin.sh@gmail.com>

;; Author: Chen Bin <chenbin.sh@gmail.com>

;; This file is not part of GNU Emacs.

;;; License:

;; This file is part of evil-matchit
;;
;; evil-matchit is free software: you can redistribute it and/or
;; modify it under the terms of the GNU General Public License as published
;; by the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.
;;
;; evil-matchit is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.
;;
;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <http://www.gnu.org/licenses/>.


;;; Code:

(require 'evil-matchit-sdk)
(require 'evil-matchit)

(defvar evilmi-javascript-matching-chars
  (string-to-list "{[(}}])"))

;; javascript code: "(function(...) { ..."
;; C code: "} else {"
;; React JS code: " return ("
;; line could ends with C++ or C comment
(defvar evilmi-javascript-open-brace-pattern
  "^[ \t]*[(}]?[$_a-zA-Z0-9]+.*\\([{(]\\)[ \t]*\\(\/\/.*\\|\/\*[^/]*\*\/\\)?$")

(defun evilmi--javascript-find-open-brace (cur-line)
  (let* (rlt)
    (cond
     ((string-match evilmi-javascript-open-brace-pattern
                    cur-line)
      (setq rlt (list 1 (match-string 1 cur-line))))
     (t
      (save-excursion
        (forward-line)
        (if (string-match "^[ \t]*{[ \t]*$" (evilmi-sdk-curline))
            (setq rlt (list 2 "{"))))))
    rlt))

;;;###autoload
(defun evilmi-javascript-get-tag ()
  ;; only handle open tag
  (cond
   ((memq (following-char)
          evilmi-javascript-matching-chars)
    (list (point)))
   (t
    (let* ((r (evilmi--javascript-find-open-brace (evilmi-sdk-curline)))
           (p (line-beginning-position)))
      (when r
        (forward-line (1- (car r)))
        (search-forward (cadr r) nil nil)
        (backward-char)
        (list p))))))

;;;###autoload
(defun evilmi-javascript-jump (rlt NUM)
  (when rlt
    (evilmi--simple-jump)
    (let* ((cur-line (evilmi-sdk-curline)))
      ;; hack for javascript
      (if (or (string-match "^[ \t]*}\)\(.*\)\; *$" cur-line)
              (string-match "^[ \t]*}\(.*\))\; *$" cur-line)
              (string-match "^[ \t]*}\])\; *$" cur-line))
          (line-end-position)
        (1+ (point))))))

(provide 'evil-matchit-javascript)
