#lang racket/base

(require racket/match
         racket/list
         racket/format
         racket/string)

(provide start-log-receiver
         log-display)

(define current-log-receiver-thread (make-parameter #f))
(define global-logger (current-logger))
(define other-level 'fatal)

;; Default a couple specific loggers one notch above their "noisy"
;; level. That way, if someone sets "all other" loggers to e.g. debug,
;; these won't get noisy. They need to be specifically cranked up.
(define logger-levels (make-hasheq '([cm-accomplice . warning]
                                     [GC . info])))

(define racket-log-file (build-path (find-system-path 'temp-dir) "racket-log"))
(with-output-to-file racket-log-file #:exists 'truncate void)

(define (update-log-receiver)
  (show-logger-levels)
  (start-log-receiver))

(define (start-log-receiver)
  (cond [(current-log-receiver-thread) => kill-thread])
  (let* ([args (append (list global-logger)
                       (flatten (for/list ([(k v) logger-levels])
                                  (list v k)))
                       (list other-level))]
         [r (apply make-log-receiver args)])
    (current-log-receiver-thread
     (thread
      (λ ()
         (let loop ()
           (match (sync r)
             [(vector l m v name)
              ;; To stderr
              (eprintf "; [~a] ~a\n" l m)
              (flush-output)
              ;; To /tmp/racket-log (can `tail -f' it)
              (with-output-to-file racket-log-file #:exists 'append
                                   (lambda ()
                                     (display (format "[~a] ~a\n" l m))))])
           (loop)))))))

(define (show-logger-levels)
  (define wid 20)
  (define (pr k v)
    (printf "; ~a ~a\n"
            (~a k
                #:min-width wid
                #:max-width wid
                #:limit-marker "...")
            v))
  (pr "Logger" "Level")
  (pr (make-string wid #\-) "-------")
  (for ([(k v) logger-levels])
    (pr k v))
  (pr "[all other]" other-level)
  (printf "; Writing ~v.\n" racket-log-file))

(define (log-display specs)
  (match specs
    [(list) (show-logger-levels)]
    [(list (and level (or 'none 'fatal 'error 'warning 'info 'debug)))
     (set! other-level level)
     (update-log-receiver)]
    [(list logger 'default)
     (hash-remove! logger-levels logger)
     (update-log-receiver)]
    [(list logger (and level (or 'none 'fatal 'error 'warning 'info 'debug)))
     (hash-set! logger-levels logger level)
     (update-log-receiver)]
    [_ (eprintf
        (string-join
         '("; Usage:"
           ",log                  -- show the levels currently in effect."
           ",log <logger> <level> -- set logger to level debug|info|warning|error|fatal|none"
           ",log <logger> default -- set logger to use the default, 'all other' level."
           ",log <level>          -- set the default level, for 'all other' loggers.\n")
         "\n; "))]))

;; Local Variables:
;; coding: utf-8
;; comment-column: 40
;; indent-tabs-mode: nil
;; require-final-newline: t
;; show-trailing-whitespace: t
;; End:
