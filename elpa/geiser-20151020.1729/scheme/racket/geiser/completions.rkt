;;; completions.rkt -- completion support

;; Copyright (C) 2009, 2010 Jose Antonio Ortega Ruiz

;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the Modified BSD License. You should
;; have received a copy of the license along with this program. If
;; not, see <http://www.xfree86.org/3.3.6/COPYRIGHT2.html#5>.

;; Start date: Sun Apr 26, 2009 19:02

#lang racket

(provide symbol-completions
         module-completions)

(require srfi/13 geiser/utils geiser/modules)

(define (filter-prefix prefix lst sort?)
  (filter (lambda (s) (string-prefix? prefix s))
          (if sort? (sort lst string<?) lst)))

(define (symbol-completions prefix)
  (filter-prefix prefix
                 (map symbol->string (namespace-mapped-symbols))
                 #t))

(define (module-completions prefix)
  (filter-prefix prefix (module-list) #f))
