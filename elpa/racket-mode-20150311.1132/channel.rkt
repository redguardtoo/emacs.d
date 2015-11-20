#lang racket/base

(require racket/match
         racket/contract)

(provide the-channel
         (struct-out msg)
         (struct-out load-gui)
         (struct-out rerun)
         rerun-default
         context-level?
         instrument-level?
         profile/coverage-level?
         put/stop)

;; Definitions for the context-level member of rerun

(define profile/coverage-levels
  ;; "sibling" levels that need instrument plus...
  '(profile    ;profiling-enabled
    coverage)) ;execute-counts-enabled

(define instrument-levels
  `(high     ;compile-context-preservation-enabled #t + instrument
    ,@profile/coverage-levels))

(define context-levels
  `(low      ;compile-context-preservation-enabled #f
    medium   ;compile-context-preservation-enabled #t
    ,@instrument-levels))

(define-syntax-rule (memq? x xs)
  (not (not (memq x xs))))

(define (context-level? v)
  (memq? v context-levels))

(define (instrument-level? v)
  (memq? v instrument-levels))

(define (profile/coverage-level? v)
  (memq? v profile/coverage-levels))

;; Messages via a channel from the repl thread to the main thread.
(define the-channel (make-channel))
(define-struct/contract msg ())
(define-struct/contract [load-gui msg] ())
(define-struct/contract [rerun msg]
  ([path          (or/c #f path-string?)]
   [memory-limit  (or/c #f exact-positive-integer?)]
   [pretty-print? boolean?]
   [context-level context-level?]))

(define rerun-default (rerun #f #f #f 'low))

;; To be called from REPL thread. Puts message for the main thread to
;; the channel, and blocks itself; main thread will kill the REPL
;; thread. Effectively "exit the thread with a return value".
(define (put/stop v) ;; msg? -> void?
  (channel-put the-channel v)
  (void (sync never-evt)))
