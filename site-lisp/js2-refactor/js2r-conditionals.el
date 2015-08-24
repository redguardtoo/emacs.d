;;; js2r-conditionals.el --- Conditional refactoring functions for js2-refactor

;; Copyright (C) 2012-2014 Magnar Sveen
;; Copyright (C) 2015 Magnar Sveen and Nicolas Petton

;; Author: Magnar Sveen <magnars@gmail.com>,
;;         Nicolas Petton <nicolas@petton.fr>
;; Keywords: conveniences

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <http://www.gnu.org/licenses/>.

;;; Code:

(require 's)

(defun js2r-ternary-to-if ()
  "Convert a ternary operator to an if-statement."
  (interactive)
  (js2r--guard)
  (save-excursion
    (let* ((ternary (js2r--closest 'js2-cond-node-p))
           (test-expr (js2-node-string (js2-cond-node-test-expr ternary)))
           (true-expr (js2-node-string (js2-cond-node-true-expr ternary)))
           (false-expr (js2-node-string (js2-cond-node-false-expr ternary)))
           (stmt (js2-node-parent-stmt ternary))
           (stmt-pre (buffer-substring (js2-node-abs-pos stmt) (js2-node-abs-pos ternary)))
           (stmt-post (s-trim (buffer-substring (js2-node-abs-end ternary) (js2-node-abs-end stmt))))
           (beg (js2-node-abs-pos stmt)))
      (goto-char beg)
      (delete-char (js2-node-len stmt))
      (insert "if (" test-expr ") {")
      (newline)
      (insert stmt-pre true-expr stmt-post)
      (newline)
      (insert "} else {")
      (newline)
      (insert stmt-pre false-expr stmt-post)
      (newline)
      (insert "}")
      (indent-region beg (point)))))

(provide 'js2r-conditionals)
;;; js2r-conditionals ends here
