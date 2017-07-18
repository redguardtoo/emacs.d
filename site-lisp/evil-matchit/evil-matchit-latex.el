;;; evil-matchit-latex.el ---latex plugin of evil-matchit

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

(defvar evilmi-latex-extract-keyword-howtos
  '(("\\\\\\([a-zA-Z]+\\(\{[a-zA-Z0-9+*_-]+\}\\)?\\)" 1)
    ))
;; (defvar evilmi-latex-regexp "\\\\\\([a-zA-Z]+\\(\{[a-zA-Z0-9+*_-]+\}\\)?\\)")

(defvar evilmi-latex-match-tags
  '((("if[a-zA-Z]+" "if") "else" "fi" "MONOGAMY")
    ("left" nil "right" "MONOGAMY")
    ("begin[a-z]+" nil "end[a-z]+")
    ("begin\{[a-zA-Z0-9+*_-]+\}" nil "end\{[a-zA-Z0-9+*_-]+\}")
    ))

;;;###autoload
(defun evilmi-latex-get-tag ()
  (let (rlt)
    (setq rlt (evilmi-sdk-get-tag evilmi-latex-match-tags evilmi-latex-extract-keyword-howtos))
    rlt))

;;;###autoload
(defun evilmi-latex-jump (rlt NUM)
  (evilmi-sdk-jump rlt NUM evilmi-latex-match-tags evilmi-latex-extract-keyword-howtos))

(provide 'evil-matchit-latex)
