;;; utils.rkt -- generic utilities

;; Copyright (C) 2009, 2010 Jose Antonio Ortega Ruiz

;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the Modified BSD License. You should
;; have received a copy of the license along with this program. If
;; not, see <http://www.xfree86.org/3.3.6/COPYRIGHT2.html#5>.

;; Start date: Sun May 03, 2009 03:09

#lang racket

(provide pair->list
         keyword->symbol
         symbol->keyword)

(define (pair->list pair)
  (let loop ([d pair] [s '()])
    (cond [(null? d) (reverse s)]
          [(symbol? d) (reverse (cons d s))]
          [else (loop (cdr d) (cons (car d) s))])))

(define keyword->symbol (compose string->symbol keyword->string))
(define (symbol->keyword sym) (string->keyword (format "~a" sym)))
