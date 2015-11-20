;;; evaluation.scm -- evaluation, compilation and macro-expansion

;; Copyright (C) 2009, 2010, 2011, 2013 Jose Antonio Ortega Ruiz

;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the Modified BSD License. You should
;; have received a copy of the license along with this program. If
;; not, see <http://www.xfree86.org/3.3.6/COPYRIGHT2.html#5>.

;; Start date: Mon Mar 02, 2009 02:46

(define-module (geiser evaluation)
  #:export (ge:compile
            ge:eval
            ge:macroexpand
            ge:compile-file
            ge:load-file
            ge:set-warnings
            ge:add-to-load-path)
  #:use-module (geiser modules)
  #:use-module (srfi srfi-1)
  #:use-module (language tree-il)
  #:use-module (system base compile)
  #:use-module (system base message)
  #:use-module (system base pmatch)
  #:use-module (system vm program)
  #:use-module (ice-9 pretty-print))


(define compile-opts '())
(define compile-file-opts '())

(define default-warnings '(arity-mismatch unbound-variable format))
(define verbose-warnings `(unused-variable ,@default-warnings))

(define (ge:set-warnings wl)
  (let* ((warns (cond ((list? wl) wl)
                      ((symbol? wl) (case wl
                                      ((none nil null) '())
                                      ((medium default) default-warnings)
                                      ((high verbose) verbose-warnings)
                                      (else '())))
                      (else '())))
         (fwarns (if (memq 'unused-variable warns)
                     (cons 'unused-toplevel warns)
                     warns)))
    (set! compile-opts (list #:warnings warns))
    (set! compile-file-opts (list #:warnings fwarns))))

(ge:set-warnings 'none)

(define (call-with-result thunk)
  (letrec* ((result #f)
            (output
             (with-output-to-string
               (lambda ()
                 (with-fluids ((*current-warning-port* (current-output-port))
                               (*current-warning-prefix* ""))
                   (with-error-to-port (current-output-port)
                     (lambda () (set! result
                                  (map object->string (thunk))))))))))
    (write `((result ,@result) (output . ,output)))
    (newline)))

(define (ge:compile form module)
  (compile* form module compile-opts))

(define (compile* form module-name opts)
  (let* ((module (or (find-module module-name) (current-module)))
         (ev (lambda ()
               (call-with-values
                   (lambda ()
                     (let* ((o (compile form
                                        #:to 'objcode
                                        #:env module
                                        #:opts opts))
                            (thunk (make-program o)))
                       (start-stack 'geiser-evaluation-stack
                                    (eval `(,thunk) module))))
                 (lambda vs vs)))))
    (call-with-result ev)))

(define (ge:eval form module-name)
  (let* ((module (or (find-module module-name) (current-module)))
         (ev (lambda ()
               (call-with-values
                   (lambda () (eval form module))
                 (lambda vs vs)))))
    (call-with-result ev)))

(define (ge:compile-file path)
  (call-with-result
   (lambda ()
     (let ((cr (compile-file path
                             #:canonicalization 'absolute
                             #:opts compile-file-opts)))
       (and cr
            (list (object->string (save-module-excursion
                                   (lambda () (load-compiled cr))))))))))

(define ge:load-file ge:compile-file)

(define (ge:macroexpand form . all)
  (let ((all (and (not (null? all)) (car all))))
    (with-output-to-string
      (lambda ()
        (pretty-print (tree-il->scheme (macroexpand form)))))))

(define (add-to-list lst dir)
  (and (not (member dir lst))))

(define (ge:add-to-load-path dir)
  (and (file-is-directory? dir)
       (let ((in-lp (member dir %load-path))
             (in-clp (member dir %load-compiled-path)))
         (when (not in-lp)
           (set! %load-path (cons dir %load-path)))
         (when (not in-clp)
           (set! %load-compiled-path (cons dir %load-compiled-path)))
         (or in-lp in-clp))))
