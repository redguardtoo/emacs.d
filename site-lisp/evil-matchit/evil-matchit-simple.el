;;; evil-matchit-simple.el --- simple match plugin of evil-matchit

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

(defun evilmi--simple-find-open-brace (cur-line)
  (if evilmi-debug (message "evilmi--simple-find-open-brace called => cur-line=%s (point)=%d" cur-line (point)))
  (let (rlt)
    ;; javascript code line "(function(...) { ..."
    ;; C code line "} else {"
    (cond
     ;; css-mode use characters ".:-"
     ((or (string-match "^[ \t]*[\(\}]?[.:_a-zA-Z0-9-]+.*{ *\\(\/\/.*\\)?$" cur-line)
          (string-match "^[ \t]*[\(\}]?[.:_a-zA-Z0-9-]+.*{ *\\(\/\*[^/]*\*\/\\)?$" cur-line))
      (setq rlt 1))
     (t
      (save-excursion
        (forward-line)
        (setq cur-line (evilmi-sdk-curline))
        (if (string-match "^[ \t]*{ *$" cur-line)
            (setq rlt 2)))))
    rlt))

;;;###autoload
(defun evilmi-simple-get-tag ()
  (let* (forward-line-num
         ;; Only handle open tag
         (tmp (evilmi--get-char-under-cursor))
         (ch (if tmp (car tmp)))
         rlt)

    (if evilmi-debug (message "evilmi-simple-get-tag called => ch=%s (point)=%d" ch (point)))

    (cond
     ;; In evil-visual-state, the (preceding-char) is actually the character under cursor
     ((not (evilmi--char-is-simple ch))
      (when (setq forward-line-num (evilmi--simple-find-open-brace (evilmi-sdk-curline)))
        (setq rlt (list (line-beginning-position)))
        ;; need handle case "if () \n { ... }".
        ;; move cursor over "{", prepare for `evil-jump-item'
        (forward-line (1- forward-line-num))
        (search-forward "{" nil nil)
        (backward-char)))
     (t
      ;; use evil's own evilmi--simple-jump
      (setq rlt (list (point)))))

    (if (and evilmi-debug rlt) (message "evilmi-simple-get-tag called rlt=%s" rlt))
    rlt))

;;;###autoload
(defun evilmi-simple-jump (rlt NUM)
  (when rlt
    (if evilmi-debug (message "evilmi-simple-jump called (point)=%d" (point)))

    ;; In latex-mode `scan-sexps' does NOT work properly between "[]"
    ;; so we have to fallback to evil's API.
    (if (memq major-mode '(latex-mode))
        (evil-jump-item)
      (evilmi--simple-jump))

    ;; hack for javascript
    (if (string-match-p "^[ \t]*})\\((.*)\\)?\; *$"
                      (evilmi-sdk-curline))
        (line-end-position)
      (1+ (point)))))

(provide 'evil-matchit-simple)
