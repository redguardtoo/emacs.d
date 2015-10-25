;;; js2r-formatting.el --- Private helper functions for formatting

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


(defun js2r--ensure-newline ()
  (if (and (not (looking-at "\s*\n"))
           (not (looking-back "\n\s*")))
      (newline-and-indent)))

(defun js2r--ensure-just-one-space ()
  (interactive)
  (while (or (looking-at "\s*\n")
             (looking-back "\n\s*"))
    (when (looking-at "\n")
      (delete-char 1))
    (when (looking-back "\n\s")
      (backward-char)
      (delete-char -1))
    (just-one-space))
  (just-one-space))

(defmacro js2r--create-bracketed-whitespace-traverser
  (name ws-fix-func looking-at-start-func
	goto-closest-start-func subexpr-str)
  "Build a function to expand or contract a given type of
   bracketed expression, i.e., function body, object literal, or
   array (any of which may be nested).
   Parameters:
       name:                    name of the function to be built
       ws-fix-func:             function to adjust whitespace at point
       looking-at-start-func:   returns t if point is at
                                    the start of the bracketed
                                    thing we want to act on
       goto-closest-start-func: moves point if necessary
                                    until looking-at-start-func
                                    is true
       subexpr-str:             literal delimiter of parts of the
                                    thing to be expanded or contracted"
  `(defun ,name ()
     (interactive)
     (save-excursion
       (if (not ,looking-at-start-func)
           ,goto-closest-start-func)
       (let ((end (make-marker)))
         (set-marker end (save-excursion
                           (forward-list)
                           (point)))
         (forward-char)
         ,ws-fix-func
         (while (< (point) end)
           (while (js2r--point-inside-string-p)
             (forward-char))
           (when (looking-at ,subexpr-str)
             (forward-char)
             ,ws-fix-func)
           (if (looking-at "\\s(")
               (forward-list)
             (forward-char)))
         (backward-char)
         ,ws-fix-func))))

(defun js2r--looking-at-object-start ()
  (and (looking-at "{")
       (not (looking-back ")[\s\n]*"))))

(defun js2r--goto-closest-object-start ()
  (while (not (js2r--looking-at-object-start))
    (if (eq (car (syntax-ppss)) 0)
        (error "Cursor is not on an object")
      (goto-char (nth 1 (syntax-ppss))))))

(js2r--create-bracketed-whitespace-traverser js2r-expand-object
					     (js2r--ensure-newline)
					     (js2r--looking-at-object-start)
					     (js2r--goto-closest-object-start)
					     ",")

(js2r--create-bracketed-whitespace-traverser js2r-contract-object
					     (js2r--ensure-just-one-space)
					     (js2r--looking-at-object-start)
					     (js2r--goto-closest-object-start)
					     ",")

(defun js2r--looking-at-array-start ()
  (looking-at "\\["))

(defun js2r--goto-closest-array-start ()
  (while (not (js2r--looking-at-array-start))
    (if (eq (car (syntax-ppss)) 0)
        (error "Cursor is not on an array")
      (goto-char (nth 1 (syntax-ppss))))))

(js2r--create-bracketed-whitespace-traverser js2r-expand-array
					     (js2r--ensure-newline)
					     (js2r--looking-at-array-start)
					     (js2r--goto-closest-array-start)
					     ",")

(js2r--create-bracketed-whitespace-traverser js2r-contract-array
					     (js2r--ensure-just-one-space)
					     (js2r--looking-at-array-start)
					     (js2r--goto-closest-array-start)
					     ",")

(defun js2r--looking-at-function-start ()
  (and (looking-at "{")
       (looking-back
	;; This horrible-looking regexp is actually pretty simple.  It
	;; matches "function <optional_name> (<optional_parameters,...>)"
	;; allowing for whitespace.  TODO: support Unicode in function and
	;; parameter names.
	(concat "function[\s\n]*"
		"\\\([a-zA-Z_$][a-zA-Z_$0-9]*[\s\n]*\\\)?"
		"\(\\\([a-zA-Z_$][a-zA-Z_$0-9]*"
		"[\s\n]*,[\s\n]*\\\)*[\s\n]*"
		"\\\([a-zA-Z_$][a-zA-Z_$0-9]*[\s\n]*\\\)*"
		"[\s\n]*\)[\s\n]*"))))

(defun js2r--goto-closest-function-start ()
  (while (not (js2r--looking-at-function-start))
    (if (eq (car (syntax-ppss)) 0)
        (error "Cursor is not on a function body")
      (goto-char (nth 1 (syntax-ppss))))))

(js2r--create-bracketed-whitespace-traverser js2r-expand-function
					     (js2r--ensure-newline)
					     (js2r--looking-at-function-start)
					     (js2r--goto-closest-function-start)
					     ";")

;; TODO: It'd be great if js2r-contract-function could recognize
;; newlines that are implied statement terminators and insert
;; semicolons correctly, but that would probably mean not using the
;; same macro as the other "contract" function definitions.
(js2r--create-bracketed-whitespace-traverser js2r-contract-function
					     (js2r--ensure-just-one-space)
					     (js2r--looking-at-function-start)
					     (js2r--goto-closest-function-start)
					     ";")

(provide 'js2r-formatting)
;;; js2-formatting.el ends here
