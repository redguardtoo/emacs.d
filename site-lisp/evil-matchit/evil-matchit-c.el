;;; evil-matchit-c.el --c like language (c/c++/perl/java/javascript) plugin of evil-matchit

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

;; ruby/bash/lua/vimrc
(defvar evilmi-c-match-tags
  '((("# *ifdef" "# *ifndef" "# *if") ("# *elif" "# *else")  "# *endif" "MONOGAMY")
    ("switch" "case" "default" "MONOGAMY")
    ))

(defvar evilmi-c-extract-keyword-howtos
  '(("^[ \t]*\\(# *[a-z]+\\)" 1)
    ("^[ \t]*\\([a-z]+\\)\\([ (:].*\\| *\\)$" 1)
    ))

;;;###autoload
(defun evilmi-c-get-tag ()
  (evilmi-sdk-get-tag evilmi-c-match-tags evilmi-c-extract-keyword-howtos))

;;;###autoload
(defun evilmi-c-jump (rlt NUM)
  (let* ((old-pos (point))
         (pos (evilmi-sdk-jump rlt NUM evilmi-c-match-tags evilmi-c-extract-keyword-howtos))
         (orig-tag (and rlt (nth 3 (cadr rlt)))))

    ;; Place cursor over last case of 'switch' statement and press %:
    ;; Should go back to beginning of switch:
    ;;   switch(c) {
    ;;   case 'a':
    ;;       break;
    ;;   case 'b':
    ;;       break;
    ;;   }
    (when (and (string= orig-tag "case")
               ;; failed to find matching tag
               (not pos))
      (goto-char old-pos)
      ;; Goto outer bracket
      (backward-up-list)
      (setq pos (beginning-of-line)))
    pos))

(provide 'evil-matchit-c)
