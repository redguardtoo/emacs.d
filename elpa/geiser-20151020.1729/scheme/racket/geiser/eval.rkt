;;; eval.rkt -- evaluation

;; Copyright (C) 2009, 2010, 2011, 2012, 2013, 2014 Jose Antonio Ortega Ruiz

;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the Modified BSD License. You should
;; have received a copy of the license along with this program. If
;; not, see <http://www.xfree86.org/3.3.6/COPYRIGHT2.html#5>.

;; Start date: Sun Apr 26, 2009 00:44

#lang racket

(provide eval-in
         load-file
         macroexpand
         add-to-load-path
         make-repl-reader
         call-with-result)

(require geiser/enter geiser/modules geiser/images)
(require errortrace/errortrace-lib)

(define last-result (void))

(define last-namespace (make-parameter (current-namespace)))

(define (exn-key e)
  (vector-ref (struct->vector e) 0))

(define (set-last-error e)
  (set! last-result `((error (key . ,(exn-key e)))))
  (display (exn-message e))
  (newline) (newline)
  (parameterize ([error-context-display-depth 10])
    (print-error-trace (current-output-port) e)))

(define (write-value v)
  (with-output-to-string
    (lambda () (maybe-write-image v))))

(define (set-last-result . vs)
  (set! last-result `((result ,@(map write-value vs)))))

(define (call-with-result thunk)
  (set-last-result (void))
  (let ([output
         (with-output-to-string
           (lambda ()
             (parameterize ([current-error-port (current-output-port)])
               (with-handlers ([exn? set-last-error])
                 (call-with-values thunk set-last-result)))))])
    (append last-result `(,(cons 'output output)))))

(define (eval-in form spec lang . non-top)
  (write (call-with-result
          (lambda ()
            (eval (if (null? non-top) (cons '#%top-interaction form) form)
                  (module-spec->namespace spec lang)))))
  (newline))

(define (load-file file)
  (load-module file (current-output-port) (last-namespace)))

(define (macroexpand form . all)
  (let ([all (and (not (null? all)) (car all))])
    (with-output-to-string
      (lambda ()
        (pretty-print (syntax->datum ((if all expand expand-once) form)))))))

(define (add-to-load-path p)
  (when (string? p)
    (let ([p (string->path p)]
          [cps (current-library-collection-paths)])
      (unless (member p cps)
        (current-library-collection-paths
         (cons p cps)))))
  #t)

(define (make-repl-reader reader)
  (lambda ()
    (last-namespace (current-namespace))
    (reader)))
