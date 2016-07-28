;;; evil-matchit-ruby.el ---ruby plugin of evil-matchit

;; Copyright (C) 2014-2016 Chen Bin <chenbin.sh@gmail.com>

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

;; OPTIONAL, you don't need SDK to write a plugin for evil-matchit
;; but SDK don make you write less code, isn't it?
;; All you need to do is just define the match-tags for SDK algorithm to lookup.
(require 'evil-matchit-sdk)

(defvar evilmi-ruby-extract-keyword-howtos
  '(("^[ \t]*\\([a-z]+\\)\\( .*\\| *\\)$" 1)
    ("^.* \\(do\\) |[a-z0-9A-Z_, ]+|$" 1)
    ("^.* \\(do\\) *$" 1)
    ("^.* \\(end\\)\\..*$" 1)
    ))

(defvar evilmi-ruby-match-tags
  '((("unless" "if") ("elsif" "else") "end")
    ("begin" ("rescue" "ensure") "end")
    ("case" ("when" "else") "end")
    (("class" "def" "while" "do" "module" "for" "until") () "end")
    ))

;;;###autoload
(defun evilmi-ruby-get-tag ()
  (let (rlt)
    (setq rlt (evilmi-sdk-get-tag evilmi-ruby-match-tags evilmi-ruby-extract-keyword-howtos))
    rlt))

;;;###autoload
(defun evilmi-ruby-jump (rlt NUM)
  (evilmi-sdk-jump rlt NUM evilmi-ruby-match-tags evilmi-ruby-extract-keyword-howtos))

(provide 'evil-matchit-ruby)
