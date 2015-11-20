#lang racket/base

(require racket/match
         racket/runtime-path
         racket/string
         "instrument.rkt"
         "util.rkt"
         "older-racket.rkt")

(provide display-exn
         our-error-display-handler
         show-full-path-in-errors)

(module+ test
  (require rackunit))

(define (display-exn exn)
  (our-error-display-handler (exn-message exn) exn))

(define (our-error-display-handler str exn)
  (when (exn? exn)
    (unless (equal? "Check failure" (exn-message exn)) ;rackunit check fails
      (display-commented (fully-qualify-error-path str))
      (display-srclocs exn)
      (unless (exn:fail:user? exn)
        (display-context exn))
      (maybe-suggest-packages exn))))

(define (display-srclocs exn)
  (when (exn:srclocs? exn)
    (let* ([srclocs ((exn:srclocs-accessor exn) exn)]
           [srclocs (cond [(or (exn:fail:read? exn)
                               (exn:fail:contract:variable? exn))
                           (cdr srclocs)] ;1st one already in exn-message
                          [(exn:fail:syntax? exn)
                           '()] ;all in exn-message, e.g. Typed Racket
                          [else srclocs])])
      (for ([srcloc srclocs])
        (display-commented (source-location->string srcloc))))))

(define (display-context exn)
  (cond [(instrumenting-enabled)
         (define p (open-output-string))
         (print-error-trace p exn)
         (match (get-output-string p)
           ["" (void)]
           [s  (display-commented (string-append "Context (errortrace):"
                                                 ;; et prepends a \n
                                                 s))])]
        [else
         (match (context->string
                 (continuation-mark-set->context (exn-continuation-marks exn)))
           ["" (void)]
           [s (display-commented (string-append "Context:\n"
                                                s))])]))

(define (context->string xs)
  ;; Limit the context in two ways:
  ;; 1. Don't go beyond error-print-context-length
  ;; 2. Don't go into "system" context that's just noisy.
  (string-join (for/list ([x xs]
                          [_ (error-print-context-length)]
                          #:unless (system-context? x))
                 (context-item->string x))
               "\n"))

(define-runtime-path run.rkt "run.rkt")
(define (system-context? ci)
  (match-define (cons id src) ci)
  (or (not src)
      (let ([src (srcloc-source src)])
        (and (path? src)
             (or (equal? src run.rkt)
                 (under-system-path? src))))))

(define (under-system-path? path)
  (match (path->collects-relative path)
    [`(collects #"mred" . ,_) #t]
    [`(collects #"racket" #"contract" . ,_) #t]
    [`(collects #"racket" #"private" . ,_) #t]
    [`(collects #"typed-racket" . ,_) #t]
    [_ #f]))

(define (context-item->string ci)
  (match-define (cons id src) ci)
  (string-append (if (or src id) " " "")
                 (if src (source-location->string src) "")
                 (if (and src id) " " "")
                 (if id (format "~a" id) "")))

;; Don't use source-location->string from syntax/srcloc. Don't want
;; the setup/path-to-relative behavior that replaces full pathnames
;; with <collects>, <pkgs> etc. Instead want full pathnames for Emacs'
;; compilation-mode. HOWEVER note that <collects> or <pkgs> might be
;; baked into exn-message string already; we handle that in
;; `fully-qualify-error-path`. Here we handle only strings we create
;; ourselves, such as for the Context "stack trace".
(define (source-location->string x)
  (match-define (srcloc src line col pos span) x)
  (format "~a:~a:~a" src (or line "1") (or col "1")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Fully qualified pathnames in error messages, so that Emacs
;; compilation-mode can do its stuff.

;; srcloc->string uses current-directory-for-user to shorten error
;; messages. But we always want full pathnames. Setting it to
;; 'pref-dir -- very unlikely user .rkt file will be there -- is
;; least-worst way AFAIK.
(define (show-full-path-in-errors)
  (current-directory-for-user (find-system-path 'pref-dir)))

;; If this looks like a Racket error message, but the filename is
;; not fully-qualified, prepend curdir to the filename.
;;
;; This covers Racket 5.3.6 and earlier. In fact, this might be
;; sufficient for _all_ versions of Racket and we don't need the
;; `show-full-path-in-errors` thing above, at all. Not yet sure.
(define (fully-qualify-error-path s)
  (match s
    [(pregexp "^([^/.]+)\\.([^.]+):(\\d+)[:.](\\d+):(.*)$"
              (list _ base ext line col more))
     (define curdir (path->string (current-directory)))
     (string-append curdir base "." ext ":" line ":" col ":" more)]
    [s (regexp-replace* #rx"<collects>"
                        s
                        (path->string (find-collects-dir)))]))

(module+ test
  (require rackunit)
  (check-equal?
   (parameterize ([current-directory "/tmp/"])
     (fully-qualify-error-path "foo.rkt:3:0: f: unbound identifier\n   in: f"))
   "/tmp/foo.rkt:3:0: f: unbound identifier\n   in: f")
  (check-equal?
   (fully-qualify-error-path "/tmp/foo.rkt:3:0: f: unbound identifier\n   in: f")
   "/tmp/foo.rkt:3:0: f: unbound identifier\n   in: f"))

(define maybe-suggest-packages
  (with-handlers ([exn:fail? (λ _ void)])
    (with-dynamic-requires ([racket/base exn:missing-module?]
                            [racket/base exn:missing-module-accessor]
                            [pkg/lib pkg-catalog-suggestions-for-module])
      (λ (exn)
        (when (exn:missing-module? exn)
          (define mod ((exn:missing-module-accessor exn) exn))
          (match (pkg-catalog-suggestions-for-module mod)
            [(list) void]
            [(list p)
             (display-commented (format "Try `raco pkg install ~a`?" p))]
            [(? list? ps)
             (display-commented (format "Try `raco pkg install` one of ~a?"
                                        (string-join ps ", ")))]
            [_ void]))))))

(module+ test
  ;; Point of this test is older Rackets where the with-handlers
  ;; clause is exercised.
  (check-not-exn
   (λ ()
     (maybe-suggest-packages (exn:fail "" (current-continuation-marks))))))

;; Local Variables:
;; coding: utf-8
;; comment-column: 40
;; indent-tabs-mode: nil
;; require-final-newline: t
;; show-trailing-whitespace: t
;; End:
