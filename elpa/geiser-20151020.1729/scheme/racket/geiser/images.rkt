;;; images.rkt -- support for image handline

;; Copyright (C) 2012, 2014 Jose Antonio Ortega Ruiz

;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the Modified BSD License. You should
;; have received a copy of the license along with this program. If
;; not, see <http://www.xfree86.org/3.3.6/COPYRIGHT2.html#5>.

;; Authors: Michael Wilber, Jose Antonio Ortega Ruiz <jao@gnu.org>
;; Start date: Sun Sep 2, 2012 18:54


#lang racket/base

(require racket/file file/convertible racket/pretty)
(provide image-cache
         maybe-print-image
         maybe-write-image
         make-port-print-handler
         make-pretty-print-size-hook
         make-pretty-print-print-hook)

(define image-cache
  (let ([ensure-dir (lambda (dir)
                      (if (path-string? dir)
                          (begin (make-directory* dir)
                                 (if (path? dir) (path->string dir) dir))
                          (path->string (find-system-path 'temp-dir))))])
    (make-parameter (ensure-dir #f) ensure-dir)))

(define (save-tmpimage imgbytes)
  ;; Save imgbytes to a new temporary file and return the filename
  (define filename (make-temporary-file "geiser-img-~a.png" #f (image-cache)))
  (with-output-to-file filename #:exists 'truncate
                       (lambda () (display imgbytes)))
  (format "#<Image: ~a>" filename))

(define (maybe-save-image value)
  (and (convertible? value)
       ;; (The above could be problematic if a future version of racket
       ;; suddenly decides it can "convert" strings to picts)
       (save-tmpimage (convert value 'png-bytes))))

(define (maybe-print-image value)
  (cond [(maybe-save-image value) => (lambda (s) (printf "~a\n" s))]
        [else (unless (void? value)
                (pretty-print value))]))

(define (maybe-write-image value)
  (write (or (maybe-save-image value) value)))

(define (make-port-print-handler ph)
  (lambda (value port . rest)
    (apply ph (or (maybe-save-image value) value) port rest)))

(define (make-pretty-print-size-hook [orig (pretty-print-size-hook)])
  (lambda (value display? port)
    (if (convertible? value)
        (pretty-print-columns)
        (orig value display? port))))

(define (make-pretty-print-print-hook [orig (pretty-print-print-hook)])
  (lambda (value display? port)
    (let [(img (maybe-save-image value))]
      (if img (print img port) (orig value display? port)))))
