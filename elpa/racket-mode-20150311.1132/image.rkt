#lang racket/base

;;; Portions Copyright (C) 2012 Jose Antonio Ortega Ruiz.

(require file/convertible
         racket/file
         racket/vector)

(provide convert-image?
         convert-image)

;; save-temporary-image : bytes? -> string?
;;
;; Write bytes to a temporary file and return "#<Image: filename>".
(define (save-temporary-image png-bytes)
  (define filename (make-temporary-file "racket-image-~a.png"))
  (with-output-to-file filename #:exists 'truncate
    (λ () (display png-bytes)))
  (format "#<Image: ~a>" filename))

(define (convert-image? v)
  (convertible? v))

(define (convert-image v)
  (cond [(and (convertible? v) (convert v 'png-bytes)) => save-temporary-image]
        [else v]))

;; Local Variables:
;; coding: utf-8
;; comment-column: 40
;; indent-tabs-mode: nil
;; require-final-newline: t
;; show-trailing-whitespace: t
;; End:
