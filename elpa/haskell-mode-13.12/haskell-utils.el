;;; haskell-utils.el --- General utility functions used by haskell-mode modules

;; Copyright (C) 2013  Herbert Valerio Riedel

;; Author: Herbert Valerio Riedel <hvr@gnu.org>

;; This file is not part of GNU Emacs.

;; This file is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 3 of the License, or
;; (at your option) any later version.

;; This file is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:

;; This module's purpose is to provide a place for helper functions
;; which are general enough to be usable by multiple modules and/or
;; to alleviate circular module dependency problems.
;;
;; When possible, functions in this module shall be accompanied by
;; ERT-based unit tests.
;;
;; See also `haskell-str.el' for string utility functions.
;;
;; All symbols in this module have a `haskell-utils-' prefix.

;;; Code:

;; NOTE: This module is supposed to be a leaf-module and shall not
;;       require/depend-on any other haskell-mode modules in order to
;;       stay at the bottom of the module dependency graph.


(defun haskell-utils-read-directory-name (prompt default)
  "Read directory name and normalize to true absolute path.
Refer to `read-directory-name' for the meaning of PROMPT and
DEFAULT."
  (let ((filename (file-truename
                   (read-directory-name prompt
                                        default
                                        default))))
    (concat (replace-regexp-in-string "/$" "" filename)
            "/")))


(defun haskell-utils-parse-import-statement-at-point ()
  "Return imported module name if on import statement or nil otherwise.
This currently assumes that the \"import\" keyword and the module
name are on the same line.

This function supports the SafeHaskell and PackageImports syntax extensions.

Note: doesn't detect if in {--}-style comment."
  (save-excursion
    (goto-char (line-beginning-position))
    (if (looking-at (concat "[\t ]*import[\t ]+"
                            "\\(?:safe[\t ]+\\)?" ;; SafeHaskell
                            "\\(?:qualified[\t ]+\\)?"
                            "\\(?:\"[^\"]*\"[\t ]+\\)?" ;; PackageImports
                            "\\([[:digit:][:upper:][:lower:]_.]+\\)"))
        (match-string-no-properties 1))))


(provide 'haskell-utils)

;;; haskell-utils.el ends here
