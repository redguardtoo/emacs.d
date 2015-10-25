;;; evil-matchit-simple.el --- simple match plugin of evil-matchit

;; Copyright (C) 2014  Chen Bin <chenbin.sh@gmail.com>


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

(require 'evil-matchit)

(defun evilmi--simple-find-open-brace (cur-line)
  (let (rlt)
    ;; javascript code line "(function(...) { ..."
    ;; C code line "} else {"
    (if (or (string-match "^[ \t]*[\(\}]?[_a-zA-Z0-9]+.*{ *\\(\/\/.*\\)?$" cur-line)
            (string-match "^[ \t]*[\(\}]?[_a-zA-Z0-9]+.*{ *\\(\/\*[^/]*\*\/\\)?$" cur-line))
        (setq rlt 1)
      (save-excursion
        (forward-line)
        (setq cur-line (buffer-substring-no-properties
                        (line-beginning-position) (line-end-position)))
        (if (string-match "^[ \t]*{ *$" cur-line)
            (setq rlt 2))
        ))
    rlt))

;;;###autoload
(defun evilmi-simple-get-tag ()
  (let (p
        tmp
        ch
        forward-line-num
        rlt
        (cur-line (buffer-substring-no-properties
                   (line-beginning-position) (line-end-position))))

    ;; Only handle open tag
    (setq tmp (evilmi--get-char-under-cursor))
    (if tmp (setq ch (car tmp)))
    (if evilmi-debug (message "evilmi-simple-get-tag called => %s" ch))

    (cond
     ;; In evil-visual-state, the (preceding-char) is actually the character under cursor
     ((not (evilmi--char-is-simple ch))
      (if (setq forward-line-num (evilmi--simple-find-open-brace cur-line))
          (when forward-line-num
            (setq p (line-beginning-position))
            (forward-line (1- forward-line-num))
            (search-forward "{" nil nil)
            (backward-char)
            (setq rlt (list p))
            )))
     (t
      ;; use evil's own evilmi--simple-jump
      (setq rlt (list (point)))))

    (if (and evilmi-debug rlt) (message "evilmi-simple-get-tag called rlt=%s" rlt))
    rlt))

;;;###autoload
(defun evilmi-simple-jump (rlt NUM)
  (let (cur-line)
    (when rlt
      (if evilmi-debug (message "evilmi-simple-jump called"))

      (evilmi--simple-jump)
      (setq cur-line (buffer-substring-no-properties
                      (line-beginning-position)
                      (line-end-position)))
      ;; hack for javascript
      (if (string-match "^[ \t]*})(.*)\; *$" cur-line)
          (line-end-position)
        (1+ (point)))
      )
    ))

(provide 'evil-matchit-simple)
