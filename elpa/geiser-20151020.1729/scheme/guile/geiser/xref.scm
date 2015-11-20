;;; xref.scm -- cross-referencing utilities

;; Copyright (C) 2009, 2010 Jose Antonio Ortega Ruiz

;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the Modified BSD License. You should
;; have received a copy of the license along with this program. If
;; not, see <http://www.xfree86.org/3.3.6/COPYRIGHT2.html#5>.

;; Start date: Mon Mar 02, 2009 02:37

(define-module (geiser xref)
  #:export (symbol-location
            generic-methods
            callers
            callees
            find-file)
  #:use-module (geiser utils)
  #:use-module (geiser modules)
  #:use-module (geiser doc)
  #:use-module (oop goops)
  #:use-module (system xref)
  #:use-module (system vm program))

(define (symbol-location sym)
  (cond ((symbol-module sym) => module-location)
        (else (let ((obj (symbol->object sym)))
                (or (and (program? obj) (program-location obj))
                    '())))))

(define (generic-methods sym)
  (let* ((gen (symbol->object sym))
         (methods (if (is-a? gen <generic>)
                      (generic-function-methods gen)
                      '())))
    (filter (lambda (x) (not (null? x)))
            (map (lambda (m)
                   (make-xref (method-procedure m) sym (symbol-module sym)))
                 methods))))

(define (make-xref proc name module)
  (and proc
       `(("location" . ,(or (program-location proc) (symbol-location name)))
         ("signature" . ,(object-signature name proc))
         ("module" . ,(or module '())))))

(define (program-location p)
  (cond ((not (program? p)) #f)
        ((program-source p 0) =>
         (lambda (s) (make-location (program-path p) (source:line s))))
        ((program-path p) => (lambda (s) (make-location s #f)))
        (else #f)))

(define (program-path p)
  (let* ((mod (program-module p))
         (name (and (module? mod) (module-name mod))))
    (and name (module-path name))))

(define (procedure-xref proc . mod-name)
  (let* ((proc-name (or (procedure-name proc) '<anonymous>))
         (mod-name (if (null? mod-name)
                       (symbol-module proc-name)
                       (car mod-name))))
    (make-xref proc proc-name mod-name)))

(define (callers sym)
  (let ((mod (symbol-module sym #t)))
    (and mod
         (apply append (map (lambda (procs)
                              (map (lambda (proc)
                                     (procedure-xref proc (car procs)))
                                   (cdr procs)))
                            (procedure-callers (cons mod sym)))))))

(define (callees sym)
  (let ((obj (symbol->object sym)))
    (and obj
         (map procedure-xref (procedure-callees obj)))))

(define (find-file path)
  (let loop ((dirs %load-path))
    (if (null? dirs) #f
        (let ((candidate (string-append (car dirs) "/" path)))
          (if (file-exists? candidate) candidate (loop (cdr dirs)))))))
