#lang racket/base

(require racket/contract
         racket/function
         racket/match
         syntax/modread)

(provide
 (contract-out
  [find-definition
   (-> string?
       (or/c #f 'kernel (list/c path-string?
                                natural-number/c
                                natural-number/c)))]
  [find-signature
   (-> string?
       (or/c #f pair?))]))

;; Try to find the definition of `str`, returning a list with the file
;; name, line and column, or #f if not found.
(define (find-definition str)
  (define src (source str))
  (and src
       (match-let ([(list id where) src])
         (match where
           ['kernel 'kernel]
           [path?
            ;; We have a source file. When possible, we want to find
            ;; the line and column within that file, too.
            (or
             ;; The main case: Look for a definition form.
             (let ([file-stx (file->syntax where #:expand? #t)])
               (match (define-in-stx id file-stx)
                 [(? syntax? stx) (list (path->string
                                         (or (syntax-source stx) where))
                                        (or (syntax-line stx) 1)
                                        (or (syntax-column stx) 0))]
                 [_ #f]))
             ;; If we can't find within the file, return file:1:0
             (list (path->string where) 1 0))]
           [_ #f]))))

;; Try to find the definition of `str`, returning its signature.
(define (find-signature str)
  (define src (source str))
  (and src
       (match-let ([(list id where) src])
         (match where
           ['kernel #f]
           [path?
            (or (let ([file-stx (file->syntax where #:expand? #f)])
                  (match (signature-in-stx id file-stx)
                    [(? syntax? stx) (syntax->datum stx)]
                    [_ #f])))]
           [_ #f]))))

;; Use `identifier-binding*' but don't trust its results. Check for a
;; couple special cases.
(define/contract (source str)
  (-> string?
      (or/c #f (list/c symbol? (or/c path? 'kernel #f))))
  (define src (identifier-binding* str))
  (and src
       (match-let ([(list id where nom-id nom-where) src])
         (match where
           ['kernel (list id 'kernel)]
           [path?
            (define file-stx (file->syntax where #:expand? #f))
            (or
             ;; First look for a possible renaming/contracting provide
             ;; involving `nom-id`. Because in that case the `id` that
             ;; `identifier-binding` gave us likely isn't used in the
             ;; definition. `renaming-provide-in-stx` will return
             ;; syntax for that actual id, which it gets from
             ;; examining the provide form. Use _that_ to search for
             ;; the definition form.
             (match (renaming-provide-in-stx nom-id file-stx)
               [(? syntax? stx) (list (syntax-e stx) where)]
               [_ #f])
             ;; Look for the case where the definition is actually
             ;; nom-id not id. This can happen e.g. with Typed Racket
             ;; definitions. Check for this using `define-in-stx` on
             ;; NON-expanded stx.
             (match (define-in-stx nom-id file-stx)
               [(? syntax? stx) (list nom-id nom-where)]
               [_ #f])
             ;; Otherwise accept what identifier-binding* said.
             (list id where))]
           [_ #f]))))

;; A wrapper for identifier-binding. Keep in mind that unfortunately
;; it can't report the definition id in the case of a contract-out and
;; a rename-out, both. Ex: For `(provide (contract-out rename orig new
;; contract))` it reports (1) the id for the contract-wrapper, and (2)
;; `new`, but NOT (3) `orig`.
(define/contract (identifier-binding* v)
  (-> (or/c string? symbol? identifier?)
      (or/c #f (list/c symbol? (or/c path? 'kernel #f)
                       symbol? (or/c path? 'kernel #f))))
  (define sym->id namespace-symbol->identifier)
  (define id (cond [(string? v)     (sym->id (string->symbol v))]
                   [(symbol? v)     (sym->id v)]
                   [(identifier? v) v]))
  (match (identifier-binding id)
    [(list source-mpi source-id
           nominal-source-mpi nominal-source-id
           source-phase import-phase nominal-export-phase)
     (define (mpi->path mpi)
       (match (resolved-module-path-name (module-path-index-resolve mpi))
         [(? path-string? path)        path]
         ['#%kernel                    'kernel]
         [(? symbol? sym)              (sym->path sym)]
         [(list (? symbol? sym) _ ...) (sym->path sym)]
         [_                            #f]))
     (list source-id         (mpi->path source-mpi)
           nominal-source-id (mpi->path nominal-source-mpi))]
    [_ #f]))

;; When module source is 'sym or '(sym sym1 ...) treat it as "sym.rkt"
;; in the current-load-relative-directory.
(define (sym->path sym)
  (build-path (current-load-relative-directory) (format "~a.rkt" sym)))

;; Return a syntax object (or #f) for the contents of `file`.
(define (file->syntax file #:expand? expand?)
  (define-values (base _ __) (split-path file))
  (parameterize ([current-load-relative-directory base]
                 [current-namespace (make-base-namespace)])
    (define stx (with-handlers ([exn:fail? (const #f)])
                  (with-module-reading-parameterization
                   (thunk
                    (with-input-from-file file read-syntax/count-lines)))))
    (if expand?
        (expand stx) ;; do this while current-load-relative-directory is set
        stx)))

(define (read-syntax/count-lines)
  (port-count-lines! (current-input-port))
  (read-syntax))

;; Given a symbol? and syntax?, return syntax? corresponding to the
;; definition.
;;
;; If `stx` is run through expand we can find things defined via
;; definer macros.
;;
;; If `stx` is not run through expand, we will miss some things,
;; however the syntax will be closer to what a human expects --
;; e.g. `(define (f x) x)` instead of `(define-values (f) (lambda (x) x))`.
(define (define-in-stx sym stx) ;;symbol? syntax? -> syntax?
  (define (eq-sym? stx)
    (if (eq? sym (syntax-e stx))
        stx
        #f))
  (syntax-case* stx
                (module #%module-begin define-values define-syntaxes
                        define define/contract
                        define-syntax struct define-struct)
                syntax-e=?
    [(module _ _ (#%module-begin . stxs))
     (ormap (λ (stx) (define-in-stx sym stx))
            (syntax->list #'stxs))]
    [(define          (s . _) . _)  (eq-sym? #'s) stx]
    [(define/contract (s . _) . _)  (eq-sym? #'s) stx]
    [(define s . _)                 (eq-sym? #'s) stx]
    [(define-values (ss ...) . _)   (ormap eq-sym? (syntax->list #'(ss ...)))
                                    (ormap eq-sym? (syntax->list #'(ss ...)))]
    [(define-syntax (s .  _) . _)   (eq-sym? #'s) stx]
    [(define-syntax s . _)          (eq-sym? #'s) stx]
    [(define-syntaxes (ss ...) . _) (ormap eq-sym? (syntax->list #'(ss ...)))
                                    (ormap eq-sym? (syntax->list #'(ss ...)))]
    [(define-struct s . _)          (eq-sym? #'s) stx]
    [(define-struct (s _) . _)      (eq-sym? #'s) stx]
    [(struct s . _)                 (eq-sym? #'s) stx]
    [(struct (s _) . _)             (eq-sym? #'s) stx]
    [_ #f]))

(define (signature-in-stx sym stx) ;;symbol? syntax? -> (or/c #f list?)
  (define (eq-sym? stx)
    (if (eq? sym (syntax-e stx))
        stx
        #f))
  (syntax-case* stx
                (module #%module-begin define-values define-syntaxes
                        define define/contract
                        define-syntax struct define-struct)
                syntax-e=?
    [(module _ _ (#%module-begin . stxs))
     (ormap (λ (stx) (signature-in-stx sym stx))
            (syntax->list #'stxs))]
    [(define          (s . as) . _) (eq-sym? #'s) #'(s . as)]
    [(define/contract (s . as) . _) (eq-sym? #'s) #'(s . as)]
    [_ #f]))

;; Given a symbol? and syntax?, return syntax? corresponding to the
;; contracted provide. Note that we do NOT want stx to be run through
;; `expand` because we want the original contract definitions (if
;; any). ** This is currently not used. If we ever add a
;; `find-provision` function, it would use this.
(define (contracting-provide-in-stx sym stx) ;;symbol? syntax? -> syntax?
  (define (eq-sym? stx)
    (if (eq? sym (syntax-e stx))
        stx
        #f))
  (syntax-case* stx
                (module #%module-begin provide provide/contract)
                syntax-e=?
    [(module _ _ (#%module-begin . ss))
     (ormap (λ (stx) (contracting-provide-in-stx sym stx))
            (syntax->list #'ss))]
    [(provide/contract . stxs)
     (for/or ([stx (syntax->list #'stxs)])
       (syntax-case stx ()
         [(s _) (eq-sym? #'s) stx]
         [_ #f]))]
    [(provide . stxs)
     (for/or ([stx (syntax->list #'stxs)])
       (syntax-case* stx (contract-out) syntax-e=?
         [(contract-out . stxs)
          (for/or ([stx (syntax->list #'stxs)])
            (syntax-case* stx (rename struct) syntax-e=?
              [(struct s _ ...)     (eq-sym? #'s) stx]
              [(struct (s _) _ ...) (eq-sym? #'s) stx]
              [(rename _ s _)       (eq-sym? #'s) stx]
              [(s _)                (eq-sym? #'s) stx]
              [_ #f]))]
         ;; Only care about contracting provides.
         ;; [s (eq-sym? #'s) stx]
         [_ #f]))]
    [_ #f]))

;; Find sym in a contracting and/or renaming provide, and return the
;; syntax for the ORIGINAL identifier (before being contracted and/or
;; renamed).
(define (renaming-provide-in-stx sym stx) ;;symbol? syntax? -> syntax?
  (define (eq-sym? stx)
    (if (eq? sym (syntax-e stx))
        stx
        #f))
  (syntax-case* stx
                (module #%module-begin provide provide/contract)
                syntax-e=?
    [(module _ _ (#%module-begin . ss))
     (ormap (λ (stx) (renaming-provide-in-stx sym stx))
            (syntax->list #'ss))]
    [(provide/contract . stxs)
     (for/or ([stx (syntax->list #'stxs)])
       (syntax-case stx ()
         [(s _) (eq-sym? #'s)]
         [_ #f]))]
    [(provide . stxs)
     (for/or ([stx (syntax->list #'stxs)])
       (syntax-case* stx (contract-out rename-out) syntax-e=?
         [(contract-out . stxs)
          (for/or ([stx (syntax->list #'stxs)])
            (syntax-case* stx (rename) syntax-e=?
              [(rename orig s _) (eq-sym? #'s) #'orig]
              [(s _)             (eq-sym? #'s) #'s]
              [_ #f]))]
         [(rename-out . stxs)
          (for/or ([stx (syntax->list #'stxs)])
            (syntax-case* stx () syntax-e=?
              [(orig s) (eq-sym? #'s) #'orig]
              [_ #f]))]
         [_ #f]))]
    [_ #f]))

;; For use with syntax-case*. When we use syntax-case for syntax-e equality.
(define (syntax-e=? a b)
  (equal? (syntax-e a) (syntax-e b)))

(module+ test
  (require racket/list
           racket/runtime-path
           rackunit)
  (define-runtime-path defn.rkt "defn.rkt")
  (when (string<=? (version) "6.0")
    (current-namespace (module->namespace defn.rkt)))
  (check-equal? (find-definition "display") 'kernel)
  (check-match (find-definition "displayln")
               (list* (pregexp "/racket/private/misc\\.rkt$") _)))

;; Local Variables:
;; coding: utf-8
;; comment-column: 40
;; indent-tabs-mode: nil
;; require-final-newline: t
;; show-trailing-whitespace: t
;; End:
