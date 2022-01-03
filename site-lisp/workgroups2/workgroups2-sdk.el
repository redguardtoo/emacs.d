;;; workgroups2-sdk.el --- sdk of workgroups2  -*- lexical-binding: t -*-

;; This file is NOT part of GNU Emacs.

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 3, or (at your option)
;; any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program; if not, see <https://www.gnu.org/licenses/>.

;;; Commentary:

;;

;;; Code:
(require 'cl-lib)
(require 'disass)

(defcustom wg-restore-remote-buffers t
  "Restore buffers that get \"t\" with `file-remote-p'."
  :type 'boolean
  :group 'workgroups)

(defvar wg-debug nil "For debugging.")

(defvar wg-special-buffer-serdes-functions
  '(wg-serialize-comint-buffer)
  "Functions providing serialization/deserialization for complex buffers.

Use `wg-support' macro and this variable will be filled
automatically.

An entry should be either a function symbol or a lambda, and should
accept a single Emacs buffer object as an argument.

When a buffer is to be serialized, it is passed to each of these
functions in turn until one returns non-nil, or the list ends.  A
return value of nil indicates that the function can't handle
buffers of that type.  A non-nil return value indicates that it
can.  The first non-nil return value becomes the buffer's special
serialization data.  The return value should be a cons, with a
deserialization function (a function symbol or a lambda) as the car,
and any other serialization data as the cdr.

When it comes time to deserialize the buffer, the deserialization
function (the car of the cons mentioned above) is passed the
wg-buf object, from which it should restore the buffer.  The
special serialization data itself can be accessed
with (cdr (wg-buf-special-data <wg-buf>)).  The deserialization
function must return the restored Emacs buffer object.

See the definitions of the functions in this list for examples of
how to write your own.")

(eval-and-compile
  ;; `wg-docar' has been used in macro.
  (defmacro wg-docar (spec &rest body)
    "do-style wrapper for `mapcar'.

\(fn (VAR LIST) BODY...)"
    (declare (indent 1))
    `(mapcar (lambda (,(car spec)) ,@body) ,(cadr spec))))

(defmacro wg-with-gensyms (syms &rest body)
  "Bind all symbols in SYMS to `gensym's, and eval BODY."
  (declare (indent 1))
  `(let (,@(mapcar (lambda (sym) `(,sym (cl-gensym))) syms)) ,@body))

(defmacro wg-dbind (args expr &rest body)
  "Bind the variables in ARGS to the result of EXPR and execute BODY.
Abbreviation of `destructuring-bind'."
  (declare (indent 2))
  `(cl-destructuring-bind ,args ,expr ,@body))

(defmacro wg-dohash (spec &rest body)
  "do-style wrapper for `maphash'.

\(fn (KEY VALUE TABLE [RESULT]) BODY...)"
  (declare (indent 1))
  (wg-dbind (key val table &optional result) spec
    `(progn (maphash (lambda (,key ,val) ,@body) ,table) ,result)))

(defmacro wg-asetf (&rest items)
  "Anaphoric `setf'."
  `(progn ,@(mapcar (lambda (pv)
                      `(let ((it ,(car pv)))
                         ;; Fix compile warn
                         (ignore it)
                         (setf ,@pv)))
                    ;; Take ITEMS, return a list of N length sublists, offset by STEP.
                    ;; Iterative to prevent stack overflow.
                    (let* (acc first-2-items)
                      (while items
                        (setq first-2-items (if (> (length items) 1) (list (nth 0 items) (nth 1 items))
                                              (list (nth 1 items))))
                        (push first-2-items acc)
                        (setq items (nthcdr 2 items)))
                      (nreverse acc)))))

(defmacro wg-destructuring-dolist (spec &rest body)
  "Loop over a list.
Evaluate BODY, destructuring LIST into SPEC, then evaluate RESULT
to get a return value, defaulting to nil.  The only hitch is that
spec must end in dotted style, collecting the rest of the list
into a var, like so: (a (b c) . rest)

\(fn (SPEC LIST [RESULT]) BODY...)"
  (declare (indent 1))
  (wg-dbind (loopspec list &optional result) spec
    (let ((rest (cdr (last loopspec))))
      (wg-with-gensyms (list-sym)
        `(let ((,list-sym ,list))
           (while ,list-sym
             (wg-dbind ,loopspec ,list-sym
               ,@body
               (setq ,list-sym ,rest)))
           ,result)))))

(defun wg-int-to-b36-one-digit (i)
  "Return a character in 0..9 or A..Z from I, and integer 0<=I<32.
Cribbed from `org-id-int-to-b36-one-digit'."
  (cond
   ((< i 10) (+ ?0 i))
   ((< i 36) (+ ?A i -10))))

(defun wg-b36-to-int-one-digit (i)
  "Turn a character 0..9, A..Z, a..z into a number 0..61.
The input I may be a character, or a single-letter string.
Cribbed from `org-id-b36-to-int-one-digit'."
  (and (stringp i) (setq i (string-to-char i)))
  (cond ((and (>= i ?0) (<= i ?9)) (- i ?0))
        ((and (>= i ?A) (<= i ?Z)) (+ (- i ?A) 10))
        (t (error "Invalid b36 character"))))

(defun wg-int-to-b36 (i)
  "Return a base 36 string from I."
  (let ((base 36) b36)
    (cl-labels ((add-digit () (push (wg-int-to-b36-one-digit (mod i base)) b36)
                           (setq i (/ i base))))
      (add-digit)
      (while (> i 0) (add-digit))
      (cl-map 'string 'identity b36))))

(defun wg-b36-to-int (str)
  "Convert STR, a base-36 string, into the corresponding integer.
Cribbed from `org-id-b36-to-int'."
  (let ((result 0))
    (mapc (lambda (i)
            (setq result (+ (* result 36)
                            (wg-b36-to-int-one-digit i))))
          str)
    result))

(defun wg-insert-before (elt list index)
  "Insert ELT into LIST before INDEX."
  (cond
   ((zerop index)
    (cons elt list))
   (t
    (push elt (cdr (nthcdr (1- index) list)))
    list)))

(defun wg-string-list-union (&optional list1 list2)
  "Return the `union' of LIST1 and LIST2, using `string=' as the test.
This only exists to get rid of duplicate lambdas in a few reductions."
  (cl-union list1 list2 :test 'string=))

(defun wg-aget (alist key &optional default)
  "Return the value of KEY in ALIST. Uses `assq'.
If PARAM is not found, return DEFAULT which defaults to nil."
  (or (cdr (assq key alist)) default))

(defun wg-aput (alist key value)
  "Return a new alist from ALIST with KEY's value set to VALUE."
  (let* ((found nil)
         (new (wg-docar (kvp alist)
                (if (not (eq key (car kvp))) kvp
                  (setq found (cons key value))))))
    (if found new (cons (cons key value) new))))

(defun wg-file-buffer-error (file error)
  "When restoring FILE's buffer fails, report ERROR."
  (message "Error while restoring a file %s:\n  %s"
           file
           (error-message-string error)))

(defun wg-symbol-of-compiled-function (object)
  "Return symbol of compiled function OBJECT."
  (let (rlt a)
    (with-temp-buffer
      (disassemble object (current-buffer))
      (goto-char (point-max))
      (re-search-backward "[ \t]+constant[ \t]+" )
      (setq a (split-string (string-trim (buffer-substring (point) (line-end-position)))
                            "[ \t]+"
                            t))
      (when (> (length a) 1)
        (setq rlt (intern (nth 1 a)))))
    rlt))

(provide 'workgroups2-sdk)
;;; workgroups2-sdk.el ends here
