;;; autodoc.rkt -- suport for autodoc echo

;; Copyright (C) 2009, 2010, 2011, 2012, 2013 Jose Antonio Ortega Ruiz

;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the Modified BSD License. You should
;; have received a copy of the license along with this program. If
;; not, see <http://www.xfree86.org/3.3.6/COPYRIGHT2.html#5>.

;; Start date: Sun May 03, 2009 14:45

#lang racket

(provide autodoc
         symbol-documentation
         module-exports
         update-signature-cache
         preload-help
         get-help)

(require racket/help
         geiser/utils
         geiser/modules
         geiser/locations)

(define loader-thread #f)

(define (preload-help)
  (set! loader-thread
        (thread (lambda ()
                  (with-output-to-string (lambda ()
                                           (help meh-i-dont-exist)))))))

(define here (current-namespace))

(define (get-help symbol mod)
  (when loader-thread
    (thread-wait loader-thread)
    (set! loader-thread #f))
  (if (eq? symbol mod)
      (get-mod-help mod)
      (with-handlers ([exn? (lambda (_) (eval `(help ,symbol) here))])
        (eval `(help ,symbol #:from ,(ensure-module-spec mod)) here))))

(define (get-mod-help mod)
  (let-values ([(ids syns) (module-identifiers mod)])
    (let ([sym (cond [(not (null? syns)) (car syns)]
                     [(not (null? ids)) (car ids)]
                     [else #f])])
      (and sym (get-help sym mod)))))

(define (symbol-documentation sym)
  (let* ([val (value sym (symbol-module sym))]
         [sign (autodoc* sym)])
    (and sign
         (list (cons "signature" (autodoc* sym #f))
               (cons "docstring" (docstring sym val sign))))))

(define (docstring sym val sign)
  (let* ([mod (assoc "module" (cdr sign))]
         [mod (if mod (cdr mod) "<unknown>")]
         [id (namespace-symbol->identifier sym)]
         [desc (if (identifier? id) (format "~%~%~a" (describe id sym)) "")])
    (if val
        (format "A ~a in module ~a.~a~a~a"
                (if (procedure? val) "procedure" "variable")
                mod
                (if (procedure? val)
                    ""
                    (format "~%~%Value:~%~%  ~a" val))
                (if (has-contract? val)
                    (format "~%~%Contract:~%~%  ~a"
                            (contract-name (value-contract val)))
                    "")
                desc)
        (format "An identifier in module ~a.~a" mod desc))))

;; Lifted from Eli's interactive.rkt
(define (describe id s)
  (define b (identifier-binding id))
  (cond
   [(not b) (format "`~s' is a toplevel (or unbound) identifier." s)]
   [(eq? b 'lexical) (format "`~s' is a lexical identifier." s)]
   [(or (not (list? b)) (not (= 7 (length b))))
    "*** internal error, racket changed ***"]
   [else
    (let-values ([(source-mod source-id
                   nominal-source-mod nominal-source-id
                   source-phase import-phase
                   nominal-export-phase)
                  (apply values b)])
      (let ([aliased (not (eq? s source-id))]
            [for-syn (eqv? source-phase 1)]
            [amod (not (equal? source-mod nominal-source-mod))]
            [aid (not (eq? s nominal-source-id))])
        (if (or aliased for-syn amod aid)
            (string-append
             "Defined"
             (if for-syn " for syntax" "")
             (if aliased (format " as `~s' " source-id) "")
             (if amod
                 (format " in module ~a\nand required~a in module ~a"
                         (module-path-index->name source-mod)
                         (if (eqv? import-phase 1) "-for-syntax" "")
                         (module-path-index->name nominal-source-mod))
                 "")
             (if aid
                 (format ",\nwhere it is defined as `~s'" nominal-source-id)
                 "")
             ".")
            "")))]))

(define (value id mod)
  (with-handlers ([exn? (const #f)])
    (dynamic-require mod id (const #f))))

(define (autodoc ids)
  (map (lambda (id) (or (autodoc* id) (list id)))
       (if (list? ids) ids '())))

(define (autodoc* id (extra #t))
  (define (val)
    (with-handlers ([exn? (const "")])
      (parameterize ([error-print-width 60])
        (format "~.a" (namespace-variable-value id)))))
  (and
   (symbol? id)
   (let* ([loc (symbol-location* id)]
          [name (car loc)]
          [path (cdr loc)]
          [sgns (and path (find-signatures path name id))]
          [value (if (and extra sgns (not (list? sgns)))
                     (list (cons "value" (val)))
                     '())]
          [mod (if (and extra sgns path)
                   (list (cons "module"
                               (module-path-name->name path)))
                   '())])
     (and sgns
          `(,id
            ("name" . ,name)
            ("args" ,@(if (list? sgns) (map format-signature sgns) '()))
            ,@value
            ,@mod)))))

(define (format-signature sign)
  (if (signature? sign)
      `(("required" ,@(signature-required sign))
        ("optional" ,@(signature-optional sign)
         ,@(let ((rest (signature-rest sign)))
             (if rest (list "...") '())))
        ("key" ,@(signature-keys sign)))
      '()))

(define signatures (make-hash))

(struct signature (required optional keys rest))

(define (find-signatures path name local-name)
  (let ([path (if (path? path) (path->string path) path)])
    (hash-ref! (hash-ref! signatures
                          path
                          (lambda () (parse-signatures path)))
               name
               (lambda () (infer-signatures local-name)))))

(define (parse-signatures path)
  (let ([result (make-hasheq)])
    (with-handlers ([exn? (lambda (e) result)])
      (with-input-from-file path
        (lambda ()
          (parameterize ([read-accept-reader #t])
            (let loop ([stx (read-syntax path)])
              (cond [(eof-object? stx) void]
                    [(syntax->datum stx) =>
                     (lambda (datum)
                       (parse-datum! datum result)
                       (loop (read-syntax path)))]
                    [else void]))))))
    result))

(define (parse-datum! datum store)
  (with-handlers ([exn? (lambda (_) void)])
    (match datum
      [`(module ,name ,lang (#%module-begin . ,forms))
       (for-each (lambda (f) (parse-datum! f store)) forms)]
      [`(module ,name ,lang . ,forms)
       (for-each (lambda (f) (parse-datum! f store)) forms)]
      [`(define ((,name . ,formals) . ,_) . ,_)
       (add-signature! name formals store)]
      [`(define (,name . ,formals) . ,_)
       (add-signature! name formals store)]
      [`(define ,name (lambda ,formals . ,_))
       (add-signature! name formals store)]
      [`(define ,name (case-lambda ,clauses ...))
       (for-each (lambda (c) (add-signature! name (car c) store))
                 (reverse clauses))]
      [`(,(or 'struct 'define-struct) ,name ,(? symbol? _)
         ,(list formals ...) . ,_)
       (add-signature! name formals store)]
      [`(,(or 'struct 'define-struct) ,name ,(list formals ...) . ,_)
       (add-signature! name formals store)]
      [`(define-for-syntax (,name . ,formals) . ,_)
       (add-signature! name formals store)]
      [`(define-for-syntax ,name (lambda ,formals . ,_))
       (add-signature! name formals store)]
      [`(define-syntax-rule (,name . ,formals) . ,_)
       (add-signature! name formals store)]
      [`(define-syntax ,name (syntax-rules ,specials . ,clauses))
       (for-each (lambda (c) (add-syntax-signature! name (cdar c) store))
                 (reverse clauses))]
      [`(define-syntax ,name (lambda ,_ (syntax-case ,_ . ,clauses)))
       (for-each (lambda (c) (add-syntax-signature! name (cdar c) store))
                 (reverse clauses))]
      [`(define-type ,_ . ,cases)
       (for-each (lambda (c) (add-signature! (car c) (cdr c) store)) cases)]
      [_ void])))

(define (add-signature! name formals store)
  (when (symbol? name)
    (hash-set! store
               name
               (cons (parse-formals formals)
                     (hash-ref store name '())))))

(define (add-syntax-signature! name formals store)
  (when (symbol? name)
    (hash-set! store
               name
               (cons (signature formals '() '() #f)
                     (hash-ref store name '())))))

(define (parse-formals formals)
  (let loop ([formals formals] [req '()] [opt '()] [keys '()])
    (cond [(null? formals)
           (signature (reverse req) (reverse opt) (reverse keys) #f)]
          [(symbol? formals)
           (signature (reverse req) (reverse opt) (reverse keys) formals)]
          [(pair? (car formals)) (loop (cdr formals)
                                       req
                                       (cons (car formals) opt)
                                       keys)]
          [(keyword? (car formals)) (let* ((kname (car formals))
                                           (arg-id (cadr formals))
                                           (name (if (pair? arg-id)
                                                     (list kname
                                                           (cadr arg-id))
                                                     (list kname))))
                                      (loop (cddr formals)
                                            req
                                            opt
                                            (cons name keys)))]
          [else (loop (cdr formals) (cons (car formals) req) opt keys)])))

(define (infer-signatures name)
  (with-handlers ([exn:fail:syntax? (const `(,(signature '(...) '() '() #f)))]
                  [exn:fail:contract:variable? (const #f)])
    (let ([v (namespace-variable-value name)])
      (if (procedure? v)
          (arity->signatures (procedure-arity v))
          'variable))))

(define (arity->signatures arity)
  (define (args count) (build-list count (const '_)))
  (define (arity->signature arity)
    (cond [(number? arity)
           (signature (args arity) '() '() #f)]
          [(arity-at-least? arity)
           (signature (args (arity-at-least-value arity)) '() '() 'rest)]))
  (define (conseq? lst)
    (cond [(< (length lst) 2) (number? (car lst))]
          [(and (number? (car lst))
                (number? (cadr lst))
                (eqv? (+ 1 (car lst)) (cadr lst)))
           (conseq? (cdr lst))]
          [else #f]))
  (cond [(and (list? arity) (conseq? arity))
         (let ((mi (apply min arity))
               (ma (apply max arity)))
           (list (signature (args mi) (args (- ma mi)) '() #f)))]
        [(list? arity) (map arity->signature arity)]
        [else (list (arity->signature arity))]))

(define (update-signature-cache path (form #f))
  (when (and (string? path)
             (or (not form)
                 (and (list? form)
                      (not (null? form))
                      (memq (car form)
                            '(define-syntax-rule struct
                               define-syntax define set! define-struct)))))
    (hash-remove! signatures path)))

(define (module-exports mod)
  (define (contracted id)
    (let ([v (value id mod)])
      (if (has-contract? v)
          (list id (cons "info" (contract-name (value-contract v))))
          (entry id))))
  (define (entry id)
    (let ((sign (eval `(,autodoc* ',id #f)
                      (module-spec->namespace mod #f #f))))
      (if sign (list id (cons "signature" sign)) (list id))))
  (define (classify-ids ids)
    (let loop ([ids ids] [procs '()] [vars '()])
      (cond [(null? ids)
             `(("procs" ,@(map entry (reverse procs)))
               ("vars" ,@(map list (reverse vars))))]
            [(procedure? (value (car ids) mod))
             (loop (cdr ids) (cons (car ids) procs) vars)]
            [else (loop (cdr ids) procs (cons (car ids) vars))])))
  (let-values ([(ids syn) (module-identifiers mod)])
    `(,@(classify-ids ids)
      ("syntax" ,@(map contracted syn))
      ("modules" ,@(map list (or (submodules mod) '()))))))
