;;; geiser-table.el -- table creation

;; Copyright (C) 2009, 2010, 2012 Jose Antonio Ortega Ruiz

;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the Modified BSD License. You should
;; have received a copy of the license along with this program. If
;; not, see <http://www.xfree86.org/3.3.6/COPYRIGHT2.html#5>.

;; Start date: Tue Jan 06, 2009 13:44



(defun geiser-table--col-widths (rows)
  (let* ((col-no (length (car rows)))
         (available (- (window-width) 2 (* 2 col-no)))
         (widths)
         (c 0))
    (while (< c col-no)
      (let ((width 0)
            (av-width (- available (* 5 (- col-no c)))))
        (dolist (row rows)
          (setq width
                (min av-width
                     (max width (length (nth c row))))))
        (push width widths)
        (setq available (- available width)))
      (setq c (1+ c)))
    (reverse widths)))

(defun geiser-table--pad-str (str width)
  (let ((len (length str)))
    (cond ((= len width) str)
          ((> len width) (concat (substring str 0 (- width 3)) "..."))
          (t (concat str (make-string (- width (length str)) ?\ ))))))

(defun geiser-table--str-lines (str width)
  (if (<= (length str) width)
      (list (geiser-table--pad-str str width))
    (with-temp-buffer
      (let ((fill-column width))
        (insert str)
        (fill-region (point-min) (point-max))
        (mapcar (lambda (s) (geiser-table--pad-str s width))
                (split-string (buffer-string) "\n"))))))

(defun geiser-table--pad-row (row)
  (let* ((max-ln (apply 'max (mapcar 'length row)))
         (result))
    (dolist (lines row)
      (let ((ln (length lines)))
        (if (= ln max-ln) (push lines result)
          (let ((lines (reverse lines))
                (l 0)
                (blank (make-string (length (car lines)) ?\ )))
            (while (< l ln)
              (push blank lines)
              (setq l (1+ l)))
            (push (reverse lines) result)))))
    (reverse result)))

(defun geiser-table--format-rows (rows widths)
  (let ((col-no (length (car rows)))
        (frows))
    (dolist (row rows)
      (let ((c 0) (frow))
        (while (< c col-no)
          (push (geiser-table--str-lines (nth c row) (nth c widths)) frow)
          (setq c (1+ c)))
        (push (geiser-table--pad-row (reverse frow)) frows)))
    (reverse frows)))

(defvar geiser-table-corner-lt "┌")
(defvar geiser-table-corner-lb "└")
(defvar geiser-table-corner-rt "┐")
(defvar geiser-table-corner-rb "┘")
(defvar geiser-table-line "─")
(defvar geiser-table-tee-t "┬")
(defvar geiser-table-tee-b "┴")
(defvar geiser-table-tee-l "├")
(defvar geiser-table-tee-r "┤")
(defvar geiser-table-crux "┼")
(defvar geiser-table-sep "│")

(defun geiser-table--insert-line (widths first last sep)
  (insert first geiser-table-line)
  (dolist (w widths)
    (while (> w 0)
      (insert geiser-table-line)
      (setq w (1- w)))
    (insert geiser-table-line sep geiser-table-line))
  (delete-char -2)
  (insert geiser-table-line last)
  (newline))

(defun geiser-table--insert-first-line (widths)
  (geiser-table--insert-line widths
                             geiser-table-corner-lt
                             geiser-table-corner-rt
                             geiser-table-tee-t))

(defun geiser-table--insert-middle-line (widths)
  (geiser-table--insert-line widths
                             geiser-table-tee-l
                             geiser-table-tee-r
                             geiser-table-crux))

(defun geiser-table--insert-last-line (widths)
  (geiser-table--insert-line widths
                             geiser-table-corner-lb
                             geiser-table-corner-rb
                             geiser-table-tee-b))

(defun geiser-table--insert-row (r)
  (let ((ln (length (car r)))
        (l 0))
    (while (< l ln)
      (insert (concat geiser-table-sep " "
                      (mapconcat 'identity
                                 (mapcar `(lambda (x) (nth ,l x)) r)
                                 (concat " " geiser-table-sep " "))
                      "  " geiser-table-sep "\n"))
      (setq l (1+ l)))))

(defun geiser-table--insert (rows)
  (let* ((widths (geiser-table--col-widths rows))
         (rows (geiser-table--format-rows rows widths)))
    (geiser-table--insert-first-line widths)
    (dolist (r rows)
      (geiser-table--insert-row r)
      (geiser-table--insert-middle-line widths))
    (kill-line -1)
    (geiser-table--insert-last-line widths)))


(provide 'geiser-table)
