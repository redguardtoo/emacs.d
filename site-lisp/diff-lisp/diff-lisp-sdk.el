;;; diff-lisp-sdk.el --- sdk -*- lexical-binding: t -*-

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

(defvar diff-lisp-ignore-whitespace nil
  "Ignore white space.")

(defvar diff-lisp-ignore-whitespace-change nil
  "Ignore white space change.")

(defvar diff-lisp-ignore-whitespace-at-eol t
  "Ignore white space at end of line.")

(defvar diff-lisp-ignore-cr-at-eol t
  "Ignore CR character at end of line.")

(defvar diff-lisp-debug nil "Debug flag.")

(defmacro diff-lisp-string-equal (a b x y)
  "Test if string A[X] equals string B[Y].
Please note the string is converted to a integer hash."
  `(eq (nth ,x ,a) (nth ,y ,b)))

(defun diff-lisp-show-v (v half-v-size)
  "Show content of V.  HALF-V-SIZE is used to get k diagonal."
  (let* ((i 0)
         (len (length v))
         k
         x
         rlt)
    (while (< i len)
      (setq x (aref v i))
      (when x
        (setq k (- i half-v-size))
        (push (format "k=%s end=(%s,%s)" k x (- x k)) rlt))
      (setq i (1+ i)))
    (nreverse rlt)))

(defun diff-lisp-file-to-string (file)
  "Read FILE into string."
  (cond
   ((and file (file-readable-p file))
    (with-temp-buffer
      (insert-file-contents file)
      (buffer-string)))
   (t
    "")))

(defmacro diff-lisp-hash (h c)
  "Do hash calculation on hash H and character C."
  `(setq ,h (mod (+ ,h (* ,h 32) ,c) most-positive-fixnum)))

(defmacro diff-lisp-hash-record (s)
  "Return hash of string S.  See xdl_hash_record from git."
  `(let ((h 5381)
         (len (length ,s))
         (i 0))
     (while (< i len)
       ;; `aref' is faster then `elt'
       (diff-lisp-hash h (aref ,s i))
       (setq i (1+ i)))
     h))

(defmacro diff-lisp-whitespace-p (c)
  "Test if C is a whitespace character."
  `(or (eq ,c 32) (eq ,c 9)))

(defmacro diff-lisp-hash-record-with-whitespace (s)
  "Return hash of string S.  See xdl_hash_record_with_whitespace from git."
  `(let ((h 5381)
         (len (length ,s))
         last
         at-eol
         c
         i
         (i 0)
         j
         (ignore-cr diff-lisp-ignore-cr-at-eol))

     (setq last (1- len))
     (while (< i len)
       (setq c (aref ,s i))
       (cond
        ;; ignore cr at eol
        ((and ignore-cr (eq c 31) (eq i last)))

        ;; handle white space rules
        ((diff-lisp-whitespace-p c)
         (setq j i)
         ;; if next character is also whitespace, ignore current character
         (while (and (< i last) (diff-lisp-whitespace-p (aref ,s (1+ i))))
           (setq i (1+ i)))
         (setq at-eol (eq i last))
         (cond
          (diff-lisp-ignore-whitespace
           ;; already handled
           )

          ((and diff-lisp-ignore-whitespace-change (not at-eol))
           (diff-lisp-hash h 32))

          ((and diff-lisp-ignore-whitespace-at-eol (not at-eol))
           (while (< j (1+ i))
             (diff-lisp-hash h (aref ,s j))
             (setq j (1+ j))))))

        (t
         (diff-lisp-hash h c)))

       (setq i (1+ i)))
     h))

(defun diff-lisp-lines-to-hash-list (lines)
  "Convert LINES to hash list."
  (let (rlt)
    (cond
     ((or diff-lisp-ignore-whitespace
          diff-lisp-ignore-whitespace-change
          diff-lisp-ignore-whitespace-at-eol
          diff-lisp-ignore-cr-at-eol)
      (dolist (line lines)
        (push (diff-lisp-hash-record-with-whitespace line) rlt)))

     (t
      (dolist (line lines)
        (push (diff-lisp-hash-record line) rlt))))

    (nreverse rlt)))
(provide 'diff-lisp-sdk)
;;; diff-lisp-sdk.el ends here
