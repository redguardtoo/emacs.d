;;; user.rkt -- global bindings visible to geiser users

;; Copyright (C) 2010, 2011, 2012, 2013, 2014 Jose Antonio Ortega Ruiz

;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the Modified BSD License. You should
;; have received a copy of the license along with this program. If
;; not, see <http://www.xfree86.org/3.3.6/COPYRIGHT2.html#5>.

;; Start date: Wed Mar 31, 2010 22:24

#lang racket

(provide init-geiser-repl run-geiser-server start-geiser)

(require (for-syntax racket/base)
         mzlib/thread
         racket/tcp
         racket/help
         geiser
         geiser/autodoc
         geiser/images
         geiser/enter
         geiser/eval
         geiser/modules)

(define top-namespace (current-namespace))
(define last-entered (make-parameter ""))

(define (do-enter mod name)
  (visit-module mod)
  (last-entered name)
  (current-namespace (module->namespace mod)))

(define (file-mod? mod)
  (and (list? mod)
       (= 2 (length mod))
       (eq? 'file (car mod))
       (path-string? (cadr mod))))

(define (submod-path mod)
  (and (list? mod)
       (eq? 'submod (car mod))
       (> (length mod) 1)
       (let ([parent (cadr mod)])
         (cond [(path-string? parent) `(submod (file ,parent) ,@(cddr mod))]
               [(file-mod? parent) mod]
               [(symbol? parent) mod]
               [else #f]))))

(define (module-error stx mod)
  (raise-syntax-error #f "Invalid module path" stx mod))

(define (enter! mod stx)
  (cond [(not mod)
         (current-namespace top-namespace)
         (last-entered "")]
        [(symbol? mod) (do-enter mod (symbol->string mod))]
        [(path-string? mod) (do-enter `(file ,mod) mod)]
        [(file-mod? mod) (do-enter mod (cadr mod))]
        [(submod-path mod) => (lambda (m) (do-enter m m))]
        [else (module-error stx mod)]))

(define (geiser-eval)
  (define geiser-main (module->namespace 'geiser))
  (define (eval-here form) (eval form geiser-main))
  (let* ([mod (read)]
         [lang (read)]
         [form (read)]
         [res (cond [(equal? form '(unquote apply))
                     (let* ([proc (eval-here (read))]
                            [args (map eval-here (read))]
                            [ev (lambda () (apply proc args))])
                       (eval-in `(,ev) mod lang #t))]
                    [else ((geiser:eval lang) form mod)])])
    (datum->syntax #f (list 'quote res))))

(define (geiser-load stx)
  (let* ([mod (read)]
         [res (call-with-result
               (lambda ()
                 (visit-module (cond [(file-mod? mod) mod]
                                     [(path-string? mod) `(file ,mod)]
                                     [(submod-path mod)]
                                     [else (module-error stx mod)]))
                 (void)))])
    (datum->syntax stx (list 'quote res))))

(define ((geiser-read prompt))
  (prompt)
  (flush-output (current-error-port))
  (flush-output (current-output-port))
  (let* ([in ((current-get-interaction-input-port))]
	 [form ((current-read-interaction) (object-name in) in)])
    (syntax-case form ()
      [(uq cmd) (eq? 'unquote (syntax-e #'uq))
       (case (syntax-e #'cmd)
         [(start-geiser) (datum->syntax #f `(list 'port ,(start-geiser)))]
         [(enter) (enter! (read) #'cmd)]
         [(geiser-eval) (geiser-eval)]
         [(geiser-load) (geiser-load #'cmd)]
         [(geiser-no-values) (datum->syntax #f (void))]
         [(add-to-load-path) (add-to-load-path (read))]
         [(set-image-cache) (image-cache (read))]
         [(help) (get-help (read) (read))]
         [(image-cache) (image-cache)]
         [(pwd) (~a (current-directory))]
         [(cd) (current-directory (~a (read)))]
         [else form])]
      [_ form])))

(define geiser-prompt
  (lambda ()
    (let ([m (namespace->module-name (current-namespace) (last-entered))])
      (printf "racket@~a> " (regexp-replace* " " m "_")))))

(define (geiser-prompt-read prompt)
  (make-repl-reader (geiser-read prompt)))

(define (geiser-loader) (module-loader (current-load/use-compiled)))

(define (install-print-handler handler)
  (let ([p (current-output-port)])
    (handler p (make-port-print-handler (handler p)))))

(define (install-print-handlers)
  (for-each install-print-handler (list port-print-handler
                                        port-write-handler
                                        port-display-handler))
  (pretty-print-print-hook (make-pretty-print-print-hook))
  (pretty-print-size-hook (make-pretty-print-size-hook)))

(define (init-geiser-repl)
  (compile-enforce-module-constants #f)
  (current-load/use-compiled (geiser-loader))
  (preload-help)
  (current-prompt-read (geiser-prompt-read geiser-prompt))
  (current-print maybe-print-image)
  (install-print-handlers))

(define (run-geiser-repl in out enforce-module-constants)
  (parameterize [(compile-enforce-module-constants enforce-module-constants)
                 (current-input-port in)
                 (current-output-port out)
                 (current-error-port out)
                 (current-load/use-compiled (geiser-loader))
                 (current-prompt-read (geiser-prompt-read geiser-prompt))
                 (current-print maybe-print-image)
                 (pretty-print-print-hook (make-pretty-print-print-hook))
                 (pretty-print-size-hook (make-pretty-print-size-hook))]
    (install-print-handlers)
    (preload-help)
    (read-eval-print-loop)))

(define server-channel (make-channel))

(define (run-geiser-server port enforce-module-constants (hostname #f))
  (run-server port
              (lambda (in out)
                (run-geiser-repl in out enforce-module-constants))
              #f
              void
              (lambda (p _ __)
                (let ([lsner (tcp-listen p 4 #f hostname)])
                  (let-values ([(_ p __ ___) (tcp-addresses lsner #t)])
                    (channel-put server-channel p)
                    lsner)))))

(define (start-geiser (port 0) (hostname #f) (enforce-module-constants #f))
  (thread (lambda ()
            (run-geiser-server port enforce-module-constants hostname)))
  (channel-get server-channel))
