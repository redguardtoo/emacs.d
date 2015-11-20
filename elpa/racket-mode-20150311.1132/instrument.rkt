#lang racket/base

(require (only-in errortrace/errortrace-key
                  errortrace-key)
         (only-in errortrace/errortrace-lib
                  print-error-trace
                  error-context-display-depth)
         (only-in errortrace/stacktrace
                  stacktrace^
                  stacktrace@
                  stacktrace-imports^)
         racket/match
         racket/unit
         "older-racket.rkt") ;for hash-clear!

(provide make-instrumented-eval-handler
         error-context-display-depth
         print-error-trace
         instrumenting-enabled
         test-coverage-enabled
         clear-test-coverage-info!
         get-test-coverage-info
         profiling-enabled
         clear-profile-info!
         get-profile-info)

;;; Core instrumenting

(define instrumenting-enabled (make-parameter #f))

;; These two parameters added to errortrace/stacktrace circa 6.0. They
;; help make-st-mark capture the original, unexpanded syntax, which is
;; nicer to report in a stack trace. Lacking that in older Rackets,
;; the srcloc is still correct and Emacs next-error will work.
(define original-stx (with-handlers ([exn:fail? (λ _ (make-parameter #f))])
                       (dynamic-require 'errortrace/stacktrace 'original-stx)))
(define expanded-stx (with-handlers ([exn:fail? (λ _ (make-parameter #f))])
                       (dynamic-require 'errortrace/stacktrace 'expanded-stx)))

(define ((make-instrumented-eval-handler orig-eval) orig-exp)
  ;; This is modeled after the one in DrRacket.
  (cond
    [(or (not (instrumenting-enabled))
         (compiled-expression? (if (syntax? orig-exp)
                                   (syntax-e orig-exp)
                                   orig-exp)))
     (orig-eval orig-exp)]
    [else
     (let loop ([exp (if (syntax? orig-exp)
                         orig-exp
                         (namespace-syntax-introduce (datum->syntax #f orig-exp)))])
       (let ([top-e (expand-syntax-to-top-form exp)])
         (syntax-case top-e (begin)
           [(begin expr ...)
            ;; Found a `begin', so expand/eval each contained
            ;; expression one at a time
            (let i-loop ([exprs (syntax->list #'(expr ...))]
                         [last-one (list (void))])
              (cond
                [(null? exprs)
                 (apply values last-one)]
                [else
                 (i-loop (cdr exprs)
                         (call-with-values
                          (λ ()
                            (call-with-continuation-prompt
                             (λ () (loop (car exprs)))
                             (default-continuation-prompt-tag)
                             (λ args
                               (apply
                                abort-current-continuation
                                (default-continuation-prompt-tag)
                                args))))
                          list))]))]
           [_else
            ;; Not `begin', so proceed with normal expand and eval
            (let* ([expanded-e (expand-syntax top-e)]
                   ;; For make-st-mark to work correctly we need to
                   ;; parameterize original-stx and expanded-stx.
                   [annotated (parameterize ([original-stx top-e]
                                             [expanded-stx expanded-e])
                                (annotate-top expanded-e
                                              (namespace-base-phase)))])
              ;; (local-require racket/pretty)
              ;; (pretty-write (list (syntax->datum top-e)
              ;;                     "=>"
              ;;                     (syntax->datum expanded-e)
              ;;                     "=>"
              ;;                     (syntax->datum annotated)))
              (orig-eval annotated))])))]))


;;; Better stack traces ("basic errortrace")

(define base-phase
  (variable-reference->module-base-phase (#%variable-reference)))

(define (with-mark mark expr phase)
  ;; This is modeled after the one in errortrace-lib. Specifically,
  ;; use `make-st-mark' for its capture of the original syntax to show
  ;; in the stack trace error message.
  (match (make-st-mark mark phase)
    [#f  expr]
    [loc (define phase-shift (- phase base-phase))
         (with-syntax ([expr expr]
                       [loc loc]
                       [errortrace-key errortrace-key]
                       [qte (syntax-shift-phase-level #'quote phase-shift)]
                       [wcm (syntax-shift-phase-level #'with-continuation-mark
                                                      phase-shift)])
           (syntax (wcm (qte errortrace-key)
                        loc
                        expr)))]))

;; print-error-trace
;;
;; Just re-provide the one from errortrace-lib because (a) it works
;; and (b) the `make-st-mark' representation is intentionally not
;; documented.


;;; Test coverage

(define test-coverage-enabled (make-parameter #f)) ;stacktrace-imports^

(define test-coverage-info (make-hasheq)) ;(hash/c syntax? mpair?).
;; This approach taken from DrR. Presumably set-mcar! is faster than a
;; box, which in turn is faster than hash-set!. The cdr cell is
;; ignored.

(define (clear-test-coverage-info!)
  (hash-clear! test-coverage-info))

(define (initialize-test-coverage-point expr) ;stacktrace-imports^
  (hash-set! test-coverage-info expr (mcons #f #f)))

(define (test-covered expr) ;stacktrace-imports^
  (define v (hash-ref test-coverage-info expr #f))
  (and v (with-syntax ([v v])
           #'(#%plain-app set-mcar! v #t))))

(define (get-test-coverage-info)
  ;; Due to macro expansion (e.g. to an `if` form), there may be
  ;; multiple data points for the exact same source location. We want
  ;; to logically OR them: If any are true, the source location is
  ;; covered.
  (define ht (make-hash)) ;; (list src pos span) => cover?
  (for* ([(stx v) (in-hash  test-coverage-info)]
         [cover?  (in-value (mcar v))]
         [loc     (in-value (list (syntax-source stx)
                                  (syntax-position stx)
                                  (syntax-span stx)))])
    (match (hash-ref ht loc 'none)
      ['none (hash-set! ht loc cover?)]
      [#f    (when cover? (hash-set! ht loc #t))]
      [#t    (void)]))
  (for/list ([(loc cover?) (in-hash ht)])
    (cons cover? loc)))

;;; Profiling

(define profile-key (gensym)) ;stacktrace-imports^

(define profiling-enabled (make-parameter #f)) ;stacktrace-imports^

(define profile-info (make-hasheq)) ;(hash/c any/c prof?)


(define (clear-profile-info!)
  (hash-clear! profile-info))

(struct prof
  (nest? ;guard nested calls
   num   ;exact-nonnegative-integer?
   time  ;exact-nonnegative-integer?
   name  ;(or/c #f symbol?)
   expr) ;syntax?
  #:mutable
  #:transparent)

(define (initialize-profile-point key name expr) ;stacktrace-imports^
  (hash-set! profile-info
             key
             (prof #f 0 0 (and (syntax? name) (syntax-e name)) expr)))

(define (register-profile-start key) ;stacktrace-imports^
  (define p (hash-ref profile-info key))
  (set-prof-num! p (add1 (prof-num p)))
  (cond [(prof-nest? p) #f]
        [else (set-prof-nest?! p #t)
              (current-process-milliseconds)]))

(define (register-profile-done key start) ;stacktrace-imports^
  (void
   (when start
     (define p (hash-ref profile-info key))
     (set-prof-nest?! p #f)
     (set-prof-time! p (+ (- (current-process-milliseconds) start)
                          (prof-time p))))))

(define (get-profile-info)
  (for/list ([x (in-list (hash-values profile-info))])
    (match-define (prof nest? count msec name stx) x)
    (list count msec name stx)))


;;; Finally, invoke the unit
(define-values/invoke-unit/infer stacktrace@)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; example

;; (parameterize ([instrumenting-enabled #t]
;;                [test-coverage-enabled #t]
;;                [profiling-enabled #f]
;;                [current-eval (make-instrumented-eval-handler (current-eval))])
;;   (namespace-require (string->path "/tmp/simple.rkt")))
;; (get-test-coverage-info)
;; (get-profile-info)
