;;; evil-matchit-script.el ---script (ruby/lua) plugin of evil-matchit

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

;; ruby/bash/lua/vimrc
(defvar evilmi-script-match-tags
  '((("unless" "if") ("elif" "elsif" "elseif" "else") ("end" "fi" "endif"))
    ("begin" ("rescue" "ensure") "end")
    ("case" ("when" "else") ("esac" "end"))
    ("for" () "end")
    (("fun!" "function!" "class" "def" "while" "function" "do") () ("end" "endfun" "endfunction"))
    ("repeat" ()  "until")
    ))

(defvar evilmi-script-extract-keyword-howtos
  '(("^.*\\(=\\|local\s\\)\s*\\(function\\)\s*.*$" 2)
    ("^\s*\\([a-z]+\!?\\)\\(\s.*\\| *\\)$" 1)
    ("^.*\s\\(do\\)\s|[a-z0-9A-Z,|]+|$" 1)))

;;;###autoload
(defun evilmi-script-get-tag ()
  (evilmi-sdk-get-tag evilmi-script-match-tags evilmi-script-extract-keyword-howtos)
  )

;;;###autoload
(defun evilmi-script-jump (rlt NUM)
  (evilmi-sdk-jump rlt NUM evilmi-script-match-tags evilmi-script-extract-keyword-howtos)
  )

(provide 'evil-matchit-script)
