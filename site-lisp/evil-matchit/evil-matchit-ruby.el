;;; evil-matchit-ruby.el ---ruby plugin of evil-matchit

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

;; OPTIONAL, you don't need SDK to write a plugin for evil-matchit
;; but SDK don make you write less code, isn't it?
;; All you need to do is just define the match-tags for SDK algorithm to lookup.
(require 'evil-matchit-sdk)

(defvar evilmi-ruby-extract-keyword-howtos
  '(("^[ \t]*\\([a-z]+\\)\\( .*\\| *\\)$" 1)
    ("^.* \\(do\\) |[a-z0-9A-Z,|]+|$" 1)
    )
  "The list of HOWTO on extracting keyword from current line.
Each howto is actually a pair. The first element of pair is the regular
expression to match the current line. The second is the index of sub-matches
to extract the keyword which starts from one. The sub-match is the match defined
between '\\(' and '\\)' in regular expression.
")

(defvar evilmi-ruby-match-tags
  '((("unless" "if") ("elsif" "else") ("end"))
    ("begin" ("rescue" "ensure") "end")
    ("case" ("when" "else") ("end"))
    (("class" "def" "while" "do" "module" "for" "until") () ("end"))
    )
  "The table we look up match tags. This is a three column table.
The first column contains the open tag(s).
The second column contains the middle tag(s).
The third column contains the closed tags(s).
The forth column is optional, t means the tags could be function exit
")

;;;###autoload
(defun evilmi-ruby-get-tag ()
  (let (rlt)
    (message "evilmi-ruby-get-tag called")
    (setq rlt (evilmi-sdk-get-tag evilmi-ruby-match-tags evilmi-ruby-extract-keyword-howtos))
    (message "rlt=%s" rlt)
    rlt))

;;;###autoload
(defun evilmi-ruby-jump (rlt NUM)
  (message "evilmi-ruby-jump called")
  (evilmi-sdk-jump rlt NUM evilmi-ruby-match-tags evilmi-ruby-extract-keyword-howtos)
  )

(provide 'evil-matchit-ruby)
