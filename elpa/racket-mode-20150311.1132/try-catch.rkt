#lang racket/base

(require (for-syntax racket/base
                     syntax/parse))

(provide try)

;; Some try/catch syntax. Because `with-handlers` can be
;; exceptionally bass-ackwards when nested (pun intended).
(define-syntax (try stx)
  (define-splicing-syntax-class catch-clause
    (pattern (~seq #:catch pred:expr id:id e:expr ...+)
             #:with handler #'[pred (lambda (id) e ...)]))
  (syntax-parse stx
    [(_ body:expr ...+ catch:catch-clause ...+)
     #'(with-handlers (catch.handler ...)
         body ...)]))

;; Local Variables:
;; coding: utf-8
;; comment-column: 40
;; indent-tabs-mode: nil
;; require-final-newline: t
;; show-trailing-whitespace: t
;; End:
