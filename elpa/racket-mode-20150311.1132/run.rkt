#lang racket/base

(require racket/cmdline
         racket/match
         racket/runtime-path
         racket/pretty
         "channel.rkt"
         "cmds.rkt"
         "error.rkt"
         "gui.rkt"
         "instrument.rkt"
         "logger.rkt"
         "older-racket.rkt"
         "util.rkt")

(module+ main
  (command-line #:args (command-output-file)
                (current-command-output-file command-output-file))
  ;; Emacs on Windows comint-mode needs buffering disabled
  (when (eq? (system-type 'os) 'windows)
    (file-stream-buffer-mode (current-output-port) 'none))
  (display (banner))
  (flush-output)
  (parameterize ([error-display-handler our-error-display-handler])
    (run rerun-default)))

(define (run rr) ;rerun? -> void?
  (match-define (rerun maybe-path-str mem-limit pretty-print? context-level) rr)
  (define-values (path dir) (path-string->path&dir maybe-path-str))
  ;; Always set current-directory and current-load-relative-directory
  ;; to match the source file.
  (current-directory dir)
  (current-load-relative-directory dir)
  ;; Make src-loc->string provide full pathnames
  (show-full-path-in-errors)
  ;; Custodian for the user REPL.
  (define user-cust (make-custodian))
  (define user-cust-box (make-custodian-box user-cust #t))
  (when mem-limit
    (custodian-limit-memory user-cust
                            (inexact->exact (round (* 1024 1024 mem-limit)))
                            user-cust))
  ;; If racket/gui/base isn't loaded, the current-eventspace parameter
  ;; doesn't exist, so make a "dummy" parameter of that name.
  (define current-eventspace (txt/gui (make-parameter #f) current-eventspace))
  (parameterize*
      ([current-custodian user-cust]
       ;; Use parameterize* so that `current-namespace` ...
       [current-namespace ((txt/gui make-base-namespace make-gui-namespace))]
       ;; ... is in effect when setting `current-eventspace` and others:
       [current-eventspace ((txt/gui void make-eventspace))]
       [compile-enforce-module-constants #f]
       [compile-context-preservation-enabled (not (eq? context-level 'low))]
       [current-eval (if (instrument-level? context-level)
                         (make-instrumented-eval-handler (current-eval))
                         (current-eval))]
       [instrumenting-enabled (instrument-level? context-level)]
       [use-compiled-file-paths (if (instrument-level? context-level)
                                   (cons (build-path "compiled" "errortrace")
                                         (use-compiled-file-paths))
                                   (use-compiled-file-paths))]
       [profiling-enabled (eq? context-level 'profile)]
       [test-coverage-enabled (eq? context-level 'coverage)])
    ;; Some context-levels need some state to be reset.
    (match context-level
      ['profile (clear-profile-info!)]
      ['coverage (clear-test-coverage-info!)]
      [_ (void)])
    ;; repl-thunk will be called from another thread -- either a plain
    ;; thread when racket/gui/base is not (yet) instantiated, or, from
    ;; (event-handler-thread (current-eventspace)).
    (define (repl-thunk)
      ;; 0. Set current-print and pretty-print hooks.
      (current-print (make-print-handler pretty-print?))
      (pretty-print-print-hook (make-pretty-print-print-hook))
      (pretty-print-size-hook (make-pretty-print-size-hook))
      ;; 1. Start logger display thread.
      (start-log-receiver)
      ;; 2. If module, load its lang info, require, and enter its namespace.
      (when (and path (module-path? path))
        (parameterize ([current-module-name-resolver repl-module-name-resolver])
          ;; exn:fail? during module load => re-run with "empty" module
          (with-handlers ([exn? (λ (x)
                                  (display-exn x)
                                  (put/stop (struct-copy rerun rr [path #f])))])
            (maybe-load-language-info path)
            (namespace-require path)
            ;; ;; Automatically run test submodule, if any:
            ;; (define submod-spec `(submod ,path test))
            ;; (when (module-declared? submod-spec)
            ;;   (dynamic-require submod-spec #f))
            (current-namespace (module->namespace path))
            (check-top-interaction))))
      ;; 3. read-eval-print-loop
      (parameterize ([current-prompt-read (make-prompt-read path)]
                     [current-module-name-resolver repl-module-name-resolver])
        ;; Note that read-eval-print-loop catches all non-break exceptions.
        (read-eval-print-loop)))
    ;; Main thread: Run repl-thunk on a plain thread, or, on the user
    ;; eventspace thread via queue-callback.
    ((txt/gui thread queue-callback) repl-thunk))
  ;; Main thread: Wait for message from REPL thread channel, or, user
  ;; custodian box event. Also catch breaks.
  (define msg
    (with-handlers ([exn:break? (λ (exn) (display-exn exn) 'break)])
      (match (sync the-channel user-cust-box)
        [(? custodian-box?)
         (display-commented
          (format "Exceeded the ~a MB memory limit you set.\n" mem-limit))
         'break]
        [msg msg])))
  (custodian-shutdown-all user-cust)
  (newline) ;; FIXME: Move this to racket-mode.el instead?
  (match msg
    ['break        (run (struct-copy rerun rr [path #f]))]
    [(? rerun? x)  (run x)]
    [(? load-gui?) (require-gui) (run rr)]))

(define (maybe-load-language-info path)
  ;; Load language-info (if any) and do configure-runtime.
  ;; Important for langs like Typed Racket.
  (define info (module->language-info path #t))
  (when info
    (define get-info ((dynamic-require (vector-ref info 0)
                                       (vector-ref info 1))
                      (vector-ref info 2)))
    (define configs (get-info 'configure-runtime '()))
    (for ([config (in-list configs)])
      ((dynamic-require (vector-ref config 0)
                        (vector-ref config 1))
       (vector-ref config 2)))
    (define cr-submod `(submod ,path configure-runtime))
    (when (module-declared? cr-submod)
      (dynamic-require cr-submod #f))))

(define (check-top-interaction)
  ;; Check that the lang defines #%top-interaction
  (unless (memq '#%top-interaction (namespace-mapped-symbols))
    (error 'repl "The module's language provides no `#%top-interaction' and\ncannot be used in a REPL.")))

;; Catch attempt to load racket/gui/base for the first time.
(define repl-module-name-resolver
  (let ([orig-resolver (current-module-name-resolver)])
    (case-lambda
      [(rmp ns)
       (orig-resolver rmp ns)]
      [(mp rmp stx)
       (repl-module-name-resolver mp rmp stx #t)]
      [(mp rmp stx load?)
       (when (and (eq? mp 'racket/gui/base) load?)
         (unless (gui-required?)
           (put/stop (load-gui))))
       (orig-resolver mp rmp stx load?)])))

;; path-string? -> (values (or/c #f path?) path?)
(define (path-string->path&dir path-str)
  (define path (and path-str
                    (not (equal? path-str ""))
                    (string? path-str)
                    (path-str->existing-file-path path-str)))
  (define dir (cond [path (define-values (base _ __) (split-path path))
                          (cond [(eq? base 'relative) (current-directory)]
                                [else base])]
                    [else (current-directory)]))
  (values path dir))

;; path-string? -> (or/c #f path?)
(define (path-str->existing-file-path path-str)
  (define (not-found s)
    (eprintf "; ~a not found\n" s)
    #f)
  (with-handlers ([exn:fail? (λ (_) (not-found path-str))])
    (define path (expand-user-path (string->path path-str)))
    (cond [(file-exists? path) path]
          [else (not-found (path->string path))])))

;; Note: The `dynamic-require`s seem to be necessary otherwise
;; file/convertible's convertible? always returns #f. Which seeems to
;; be a namespace issue that I don't understand.
(define-runtime-path image.rkt "image.rkt")

(define (make-print-handler pretty-print?)
  (cond [pretty-print? pretty-print-handler]
        [else (make-plain-print-handler)]))

(define (make-plain-print-handler)
  (let ([convert (dynamic-require image.rkt 'convert-image)])
    (λ (v)
      (void (unless (void? v)
              (print (convert v))
              (newline))))))

(define (make-pretty-print-size-hook [orig (pretty-print-print-hook)])
  (let ([convert? (dynamic-require image.rkt 'convert-image?)]
        [width (floor (/ (pretty-print-columns) 4))]) ;magic number? yep.
    (λ (value display? port)
      (cond [(convert? value) width]
            [else (orig value display? port)]))))

(define (make-pretty-print-print-hook [orig (pretty-print-size-hook)])
  (let ([convert? (dynamic-require image.rkt 'convert-image?)]
        [convert  (dynamic-require image.rkt 'convert-image)])
    (λ (value display? port)
      (cond [(convert? value) (print (convert value) port)]
            [else (orig value display? port)]))))

;; Local Variables:
;; coding: utf-8
;; comment-column: 40
;; indent-tabs-mode: nil
;; require-final-newline: t
;; show-trailing-whitespace: t
;; End:
