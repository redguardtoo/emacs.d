;;; emacs.scm -- procedures for emacs interaction: entry point

;; Copyright (C) 2009, 2010, 2011 Jose Antonio Ortega Ruiz

;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the Modified BSD License. You should
;; have received a copy of the license along with this program. If
;; not, see <http://www.xfree86.org/3.3.6/COPYRIGHT2.html#5>.

;; Start date: Sun Feb 08, 2009 18:39

(define-module (geiser emacs)
  #:use-module (ice-9 match)
  #:use-module (system repl command)
  #:use-module (system repl error-handling)
  #:use-module (system repl server)
  #:use-module (geiser evaluation)
  #:use-module ((geiser modules) #:renamer (symbol-prefix-proc 'ge:))
  #:use-module ((geiser completion) #:renamer (symbol-prefix-proc 'ge:))
  #:use-module ((geiser xref) #:renamer (symbol-prefix-proc 'ge:))
  #:use-module ((geiser doc) #:renamer (symbol-prefix-proc 'ge:)))

(define this-module (resolve-module '(geiser emacs)))

(define-meta-command ((geiser-no-values geiser) repl)
  "geiser-no-values
No-op command used internally by Geiser."
  (values))

(define-meta-command ((geiser-newline geiser) repl)
  "geiser-newline
Meta-command used by Geiser to emit a new line."
  (newline))

(define-meta-command ((geiser-eval geiser) repl (mod form args) . rest)
  "geiser-eval module form args ()
Meta-command used by Geiser to evaluate and compile code."
  (if (null? args)
      (call-with-error-handling
       (lambda () (ge:compile form mod)))
      (let ((proc (eval form this-module)))
        (ge:eval `(,proc ,@args) mod))))

(define-meta-command ((geiser-load-file geiser) repl file)
  "geiser-load-file file
Meta-command used by Geiser to load and compile files."
  (call-with-error-handling
   (lambda () (ge:compile-file file))))


(define-meta-command ((geiser-start-server geiser) repl)
  "geiser-start-server
Meta-command used by Geiser to start a REPL server."
  (let* ((sock (make-tcp-server-socket #:port 0))
         (port (sockaddr:port (getsockname sock))))
    (spawn-server sock)
    (write (list 'port port))
    (newline)))
