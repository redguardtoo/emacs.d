;;; haskell-show.el --- A pretty printer for Haskell Show values

;; Copyright (C) 2011  Chris Done

;; Author: Chris Done <chrisdone@gmail.com>

;; This file is not part of GNU Emacs.

;; This program is free software: you can redistribute it and/or
;; modify it under the terms of the GNU General Public License as
;; published by the Free Software Foundation, either version 3 of the
;; License, or (at your option) any later version.

;; This program is distributed in the hope that it will be useful, but
;; WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;; General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see
;; <http://www.gnu.org/licenses/>.

;;; Commentary:

;; It doesn't support some number literals (probably).  I'm not
;; precisely sure what values Show will always produce.  There is
;; however a test suite available, so patches for extra Show support
;; is welcome and should be easy to test.

;;; Code:

(defvar sexp-show "sexp-show")
(require 'cl-lib)
(require 'haskell-string)

(defun haskell-show-replace-region ()
  "Replace the given region with a pretty printed version."
  (interactive)
  (haskell-show-replace (region-beginning) (region-end)))

;;;###autoload
(defun haskell-show-replace (start end)
  "Replace the given region containing a Show value with a pretty
  printed collapsible version."
  (let ((text (buffer-substring-no-properties start end)))
    (goto-char start)
    (delete-region start end)
    (haskell-show-parse-and-insert text)))

;;;###autoload
(defun haskell-show-parse-and-insert (given)
  "Parse a `string' containing a Show instance value and insert
  it pretty printed into the current buffer."
  (when (not (string= "" (haskell-trim given)))
    (let ((current-column (- (point)
                             (line-beginning-position)))
          (result (haskell-show-parse given)))
      (if (string-match "^[\\(]" result)
          (let ((v (read result)))
            (if (equal (car v) 'arbitrary)
                (insert given)
              (haskell-show-insert-pretty current-column v)))
        (insert given)))))

;;;###autoload
(defun haskell-show-parse (given)
  "Parse the given input into a tree."
  (with-temp-buffer
    (insert given)
    (shell-command-on-region
     (point-min)
     (point-max)
     sexp-show
     t)
    (buffer-substring-no-properties (point-min) (point-max))))

(defun haskell-show-insert-pretty (column tree &optional parens)
  "Insert a Show `tree' into the current buffer with collapsible nodes."
  (cl-case (car tree)
    ('list (let ((start (point)))
             (insert "[")
             (haskell-show-mapcar/i (lambda (x i len)
                                      (haskell-show-insert-pretty (+ column 1) x)
                                      (unless (> i (- len 2))
                                        (if (< (+ column (length (haskell-show-pretty tree parens)))
                                               80)
                                            (insert ",")
                                          (insert (concat ",\n" (haskell-show-indent (+ 1 column) ""))))))
                                    (cdr tree))
             (insert "]")))
    ('tuple (let ((start (point)))
              (insert "(")
              (haskell-show-mapcar/i (lambda (x i len)
                                       (haskell-show-insert-pretty (+ column 1) x)
                                       (unless (> i (- len 2))
                                         (if (< (+ column (length (haskell-show-pretty tree parens)))
                                                80)
                                             (insert ",")
                                           (insert (concat ",\n" (haskell-show-indent (+ 1 column) ""))))))
                                     (cdr tree))
              (insert ")")))
    ('record
     (let ((record (cdr tree)) (overlay (list 'nil)))
       (insert (if parens "(" ""))
       (let ((link-start (point)))
         (insert (car record))
         (let ((button (make-text-button link-start (point) :type 'haskell-show-toggle-button)))
           (put-text-property link-start (point) 'font-lock-face 'font-lock-type-face)
           (button-put button 'overlay overlay)))
       (insert " {\n")
       (let ((curly-start (1- (point)))
             (show-len (+ column (length (haskell-show-pretty tree parens)))))
         (haskell-show-mapcar/i (lambda (field i len)
                                  (insert
                                   (haskell-show-indent
                                    (if (and (> i 0) (< show-len 80)) 0 column)
                                    (car field)))
                                  (insert " = ")
                                  (put-text-property (- (point) 3) (point) 'font-lock-face
                                                     'font-lock-constant-face)
                                  (haskell-show-insert-pretty
                                   (if (< show-len 80)
                                       0
                                     (+ (length (car field)) column 3))
                                   (cdr field))
                                  (unless (> i (- len 2))
                                    (if (< show-len 80)
                                        (insert ", ")
                                      (insert ",\n"))))
                                (cdr record))
         (insert (concat "\n" (haskell-show-indent column "}")))
         (progn
           (setf (car overlay) (make-overlay curly-start (- (point) 1) nil t))
           (overlay-put (car overlay) 'invisible t))
         (insert (if parens ")" "")))))
    ('num (let ((num-start (point)))
            (insert (format "%d" (cdr tree)))
            (put-text-property num-start (point) 'font-lock-face 'font-lock-constant-face)))
    ('string (let ((str-start (point)))
               (insert "\"")
               (if (< (+ column (length (cdr tree))) 60)
                   (progn
                     (insert (format "%s" (cdr tree)))
                     (put-text-property (+ 1 str-start) (point) 'font-lock-face 'font-lock-string-face))
                 (progn
                   (insert "…")
                   (insert (format "%s" (cdr tree)))
                   (let ((overlay (make-overlay (+ 2 str-start) (point) nil t)))
                     (overlay-put overlay 'invisible t)
                     (put-text-property (+ 2 str-start) (point) 'font-lock-face 'font-lock-string-face)
                     (let ((button (make-text-button (+ 1 str-start) (+ 2 str-start)
                                                     :type 'haskell-show-toggle-button)))
                       (put-text-property (+ 1 str-start) (+ 2 str-start)
                                          'font-lock-face 'font-lock-keyword-face)
                       (button-put button 'overlay (list overlay))
                       (button-put button 'hide-on-click t)))))
               (insert "\"")))
    ('data (let ((data (cdr tree)))
             (insert (if parens "(" ""))
             (let ((cons-start (point)))
               (insert (car data))
               (put-text-property cons-start (point) 'font-lock-face 'font-lock-type-face))
             (unless (null (cdr data))
               (progn (insert " ")
                      (haskell-show-mapcar/i
                       (lambda (x i len)
                         (haskell-show-insert-pretty column x t)
                         (unless (> i (- len 2))
                           (insert " ")))
                       (cdr data))))
             (insert (if parens ")" ""))))
    ('char (progn (insert "'")
                  (insert (char-to-string (cdr tree)))
                  (put-text-property (- (point) 1) (point) 'font-lock-face 'font-lock-string-face)
                  (insert "'")))
    ('arbitrary (let ((start (point)))
                  (insert (cdr tree))
                  (put-text-property start (point) 'font-lock-face 'font-lock-comment-face)))
    (otherwise (error "Unsupported node type: %S" tree))))

(define-button-type 'haskell-show-toggle-button
  'action 'haskell-show-toggle-button-callback
  'follow-link t
  'help-echo "Click to expand…")

(defun haskell-show-toggle-button-callback (btn)
  "The callback to toggle the overlay visibility."
  (let ((overlay (button-get btn 'overlay)))
    (when overlay
      (overlay-put (car overlay)
                   'invisible (not (overlay-get (car overlay)
                                                'invisible)))))
  (let ((hide (button-get btn 'remove-on-click)))
    (when hide
      (button-put btn 'invisible t))))

(defun haskell-show-pretty (tree &optional parens)
  "Show a Show `tree'."
  (cl-case (car tree)
    ('list (format "[%s]"
                   (mapconcat
                    (lambda (x)
                      (haskell-show-pretty x))
                    (cdr tree)
                    ",")))
    ('record (let ((record (cdr tree)))
               (format "%s%s {%s}%s"
                       (if parens "(" "")
                       (car record)
                       (mapconcat (lambda (field)
                                    (format "%s = %s"
                                            (car field)
                                            (haskell-show-pretty (cdr field))))
                                  (cdr record)
                                  ", ")
                       (if parens ")" ""))))
    ('num (format "%s" (cdr tree)))
    ('string (format "%S" (cdr tree)))
    ('data (let ((data (cdr tree)))
             (format "%s%s%s%s"
                     (if parens "(" "")
                     (car data)
                     (if (null (cdr data))
                         ""
                       (concat " "
                               (mapconcat
                                (lambda (x) (haskell-show-pretty x t))
                                (cdr data)
                                " ")))
                     (if parens ")" ""))))
    ('tuple (format "(%s)"
                    (mapconcat
                     (lambda (x)
                       (haskell-show-pretty x))
                     (cdr tree)
                     ",")))
    ('char (format "'%s'" (if (= (cdr tree) ?')
                              "\\'"
                            (char-to-string (cdr tree)))))
    ('arbitrary (cdr tree))
    (otherwise (error "Unsupported node type: %S" tree))))

(defun haskell-show-mapcar/i (f xs)
  "Map `f' across `xs' giving the index and length to `f' as extra parameters."
  (let ((len (length xs))
        (i 0))
    (mapcar (lambda (x)
              (funcall f x i len)
              (setq i (1+ i)))
            xs)))

(defun haskell-show-indent (n s)
  "Indent a string `s' at colum `n'."
  (concat (make-string n ? )
          s))

(provide 'haskell-show)

;;; haskell-show.el ends here
