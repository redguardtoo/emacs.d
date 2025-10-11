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

(defsubst diff-lisp-string-equal (a b x y)
  "Test if hash at A[X] equals hash at B[Y]."
  (= (aref a x) (aref b y)))

(defun diff-lisp-file-to-string (file)
  "Read FILE into string."
  (if (and file (file-readable-p file))
      (with-temp-buffer
        (insert-file-contents file)
        (buffer-string))
    ""))

(defsubst diff-lisp-hash (h c)
  "Update hash H with character code C."
  (mod (+ h (* h 32) c) most-positive-fixnum))

(defsubst diff-lisp-hash-record (s)
  "Return hash of string S.  See xdl_hash_record from git."
  (let ((h 5381)
        (len (length s)))
    (dotimes (i len h)
      (setq h (diff-lisp-hash h (aref s i))))
  h))

(defsubst diff-lisp-whitespace-p (c)
  "Test if C is a whitespace character (space or tab)."
  (or (= c 32) (= c 9)))

(defmacro diff-lisp-spaces-hash (hash first last)
  "Get HASH of consecutive space characters with index of FIRST and LAST."
  `(while (<= ,first ,last)
            (setq ,hash (diff-lisp-hash ,hash 32))
            (setq ,first (1+ ,first))))

(defsubst diff-lisp-hash-record-with-whitespace (s)
  "Return hash of string S with whitespace rules.
See xdl_hash_record_with_whitespace from git."
  (let* ((h 5381)
         (len (length s))
         (ignore-cr diff-lisp-ignore-cr-at-eol)
         (last (1- len))
         (i 0)
         j
         at-eol
         c)
    (while (< i len)
      (setq c (aref s i))
      (cond

       ;; ignore CR at eol (Windows-style line ending)
       ((and ignore-cr (= c 13) (= i last)))

       ;; whitespace rules
       ((diff-lisp-whitespace-p c)
        (setq j i)
        ;; coalesce consecutive whitespace
        (while (and (< i last)
                    (diff-lisp-whitespace-p (aref s (1+ i))))
          (setq i (1+ i)))
        (setq at-eol (= i last))
        (cond
         ;; ignore all whitespace
         (diff-lisp-ignore-whitespace)

         ;; space sequences in the middle regarded as single space
         ((and diff-lisp-ignore-whitespace-change (not at-eol))
          (setq h (diff-lisp-hash h 32)))

         ;; skip trailing spaces
         ((and diff-lisp-ignore-whitespace-change at-eol))

         ((and diff-lisp-ignore-whitespace-at-eol (not at-eol))
          ;; keep original white spaces between j..i
          (diff-lisp-spaces-hash h j i))

         ;; skip trailing spaces
         ((and diff-lisp-ignore-whitespace-at-eol at-eol))

         ;; count all spaces
         (t
          (diff-lisp-spaces-hash h j i))))

       ;; normal character
       (t
        (setq h (diff-lisp-hash h c))))
      (setq i (1+ i)))

    h))

(defsubst diff-lisp-line-to-hash (lines)
  "Convert each item of LINES into efficient hash."
  (let* ((len (length lines))
         (rlt (make-vector len nil)))
    (cond
     ((or diff-lisp-ignore-whitespace
          diff-lisp-ignore-whitespace-change
          diff-lisp-ignore-whitespace-at-eol
          diff-lisp-ignore-cr-at-eol)
      (dotimes (i len)
        (aset rlt i (diff-lisp-hash-record-with-whitespace (aref lines i)))))
     (t
      (dotimes (i len)
        (aset rlt i (diff-lisp-hash-record (aref lines i))))))
     rlt))

(provide 'diff-lisp-sdk)
;;; diff-lisp-sdk.el ends here
