;;; doc.scm -- procedures providing documentation on scheme objects

;; Copyright (C) 2009, 2010 Jose Antonio Ortega Ruiz

;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the Modified BSD License. You should
;; have received a copy of the license along with this program. If
;; not, see <http://www.xfree86.org/3.3.6/COPYRIGHT2.html#5>.

;; Start date: Sun Feb 08, 2009 18:44

(define-module (geiser doc)
  #:export (autodoc
            symbol-documentation
            module-exports
            object-signature)
  #:use-module (geiser utils)
  #:use-module (geiser modules)
  #:use-module (system vm program)
  #:use-module (ice-9 session)
  #:use-module (ice-9 documentation)
  #:use-module (ice-9 regex)
  #:use-module (ice-9 format)
  #:use-module (oop goops)
  #:use-module (srfi srfi-1))

(define (autodoc ids)
  (if (not (list? ids))
      '()
      (map (lambda (id) (or (autodoc* id) (list id))) ids)))

(define* (autodoc* id)
  (let ((args (obj-args (symbol->object id))))
    (and args
         `(,@(signature id args)
           ("module" . ,(symbol-module id))))))

(define (object-signature name obj)
  (let ((args (obj-args obj)))
    (and args (signature name args))))

(define (value-str obj)
  (format #f "~:@y" obj))

(define* (signature id args-list #:optional (detail #t))
  (define (arglst args kind)
    (let ((args (assq-ref args kind)))
      (cond ((or (not args) (null? args)) '())
            ((list? args) args)
            (else (list args)))))
  (define (mkargs as)
    `(("required" ,@(arglst as 'required))
      ("optional" ,@(arglst as 'optional)
       ,@(if (assq-ref as 'rest) (list "...") '()))
      ("key" ,@(arglst as 'keyword))))
  (let* ((args-list (map mkargs (if (list? args-list) args-list '())))
         (value (and (and detail (null? args-list))
                     (value-str (symbol->object id)))))
    `(,id ("args" ,@args-list) ,@(if value `(("value" . ,value)) '()))))

(define default-macro-args '(((required ...))))

(define geiser-args-key (gensym "geiser-args-key-"))

(define (obj-args obj)
  (cond ((not obj) #f)
        ((or (procedure? obj) (program? obj))
         (cond ((procedure-property obj geiser-args-key))
               ((arguments obj) =>
                (lambda (args)
                  (set-procedure-property! obj geiser-args-key args)
                  args))
               (else #f)))
        ((and (macro? obj) (macro-transformer obj)) => macro-args)
        ((macro? obj) default-macro-args)
        (else 'variable)))

(define (arguments proc)
  (define (p-args prog)
    (let ((as (map (lambda (a)
                     ((@@ (system vm program) arity->arguments-alist) prog a))
                     (or (program-arities prog) '()))))
      (and (not (null? as)) as)))
  (define (clist f) (lambda (x) (let ((y (f x))) (and y (list y)))))
  (cond ((is-a? proc <generic>) (generic-args proc))
        ((doc->args proc) => list)
        ((procedure-property proc 'arglist) => (clist arglist->args))
        ((procedure-source proc) => (clist source->args))
        ((and (program? proc) (p-args proc)))
        ((procedure-property proc 'arity) => (clist arity->args))
        (else #f)))

(define (source->args src)
  (let ((formals (cadr src)))
    (cond ((list? formals) `((required . ,formals)))
          ((pair? formals)
           `((required . ,(car formals)) (rest . ,(cdr formals))))
          (else #f))))

(define (macro-args tf)
  (define* (collect args #:optional (req '()))
    (cond ((null? args) (arglist->args `(,(reverse req) #f #f r #f)))
          ((symbol? args) (arglist->args `(,(reverse req) #f #f r ,args)))
          ((and (pair? args) (symbol? (car args)))
           (collect (cdr args) (cons (car args) req)))
          (else #f)))
  (let* ((pats (procedure-property tf 'patterns))
         (args (and pats (filter-map collect pats))))
    (or (and args (not (null? args)) args) default-macro-args)))

(define (arity->args art)
  (define (gen-arg-names count)
    (map (lambda (x) '_) (iota (max count 0))))
  (let ((req (car art))
        (opt (cadr art))
        (rest (caddr art)))
    `(,@(if (> req 0)
            (list (cons 'required (gen-arg-names req)))
            '())
      ,@(if (> opt 0)
            (list (cons 'optional (gen-arg-names opt)))
            '())
      ,@(if rest (list (cons 'rest 'rest)) '()))))

(define (arglist->args arglist)
  `((required . ,(car arglist))
    (optional . ,(cadr arglist))
    (keyword . ,(caddr arglist))
    (rest . ,(car (cddddr arglist)))))

(define (doc->args proc)
  ;; Guile 2.0.9+ uses the (texinfo ...) modules to produce
  ;; `guile-procedures.txt', and the output has a single hyphen, whereas
  ;; `makeinfo' produces two hyphens.
  (define proc-rx "--? Scheme Procedure: ([^[\n]+)\n")
  (define proc-rx2 "--? Scheme Procedure: ([^[\n]+\\[[^\n]*(\n[^\n]+\\]+)?)")
  (let ((doc (object-documentation proc)))
    (and doc
         (let ((match (or (string-match proc-rx doc)
                          (string-match proc-rx2 doc))))
           (and match
                (parse-signature-string (match:substring match 1)))))))

(define (parse-signature-string str)
  (define opt-arg-rx "\\[([^] ]+)\\]?")
  (define opt-arg-rx2 "([^ ])+\\]+")
  (let ((tokens (string-tokenize str)))
    (if (< (length tokens) 2)
        '()
        (let loop ((tokens (cdr tokens)) (req '()) (opt '()) (rest #f))
          (cond ((null? tokens)
                 `((required ,@(map string->symbol (reverse! req)))
                   (optional ,@(map string->symbol (reverse! opt)))
                   ,@(if rest
                         (list (cons 'rest (string->symbol rest)))
                         '())))
                ((string=? "." (car tokens))
                 (if (not (null? (cdr tokens)))
                     (loop (cddr tokens) req opt (cadr tokens))
                     (loop '() req opt "rest")))
                ((or (string-match opt-arg-rx (car tokens))
                     (string-match opt-arg-rx2 (car tokens)))
                 => (lambda (m)
                      (loop (cdr tokens)
                            req
                            (cons (match:substring m 1) opt)
                            rest)))
                (else (loop (cdr tokens)
                            (cons (car tokens) req)
                            opt
                            rest)))))))

(define (generic-args gen)
  (define (src> src1 src2)
    (> (length (cadr src1)) (length (cadr src2))))
  (define (src m)
    (catch #t
      (lambda () (method-source m))
      (lambda (k . a) #f)))
  (let* ((methods (generic-function-methods gen))
         (srcs (filter identity (map src methods))))
    (cond ((and (null? srcs)
                (not (null? methods))
                (method-procedure (car methods))) => arguments)
          ((not (null? srcs)) (list (source->args (car (sort! srcs src>)))))
          (else '(((rest . rest)))))))

(define (symbol-documentation sym)
  (let ((obj (symbol->object sym)))
    (if obj
        `(("signature" . ,(or (obj-signature sym obj #f) sym))
          ("docstring" . ,(docstring sym obj))))))

(define (docstring sym obj)
  (define (valuable?)
    (not (or (macro? obj) (procedure? obj) (program? obj))))
  (with-output-to-string
    (lambda ()
      (let* ((type (cond ((macro? obj) "A macro")
                         ((procedure? obj) "A procedure")
                         ((program? obj) "A compiled program")
                         (else "An object")))
             (modname (symbol-module sym))
             (doc (object-documentation obj)))
        (display type)
        (if modname
            (begin
              (display " in module ")
              (display modname)
              (display ".")))
        (newline)
        (if doc (begin (newline) (display doc)))
        (if (valuable?) (begin (newline)
                               (display "Value:")
                               (newline)
                               (display "   ")
                               (display (value-str obj))))))))

(define* (obj-signature sym obj #:optional (detail #t))
  (let ((args (obj-args obj)))
    (and args (signature sym args detail))))

(define (module-exports mod-name)
  (define elt-sort (make-symbol-sort car))
  (let* ((mod (catch #t
                (lambda () (resolve-interface mod-name))
                (lambda args (resolve-module mod-name))))
         (elts (hash-fold classify-module-object
                          (list '() '() '())
                          (module-obarray mod)))
         (elts (map elt-sort elts))
         (subs (map (lambda (m) (list (module-name m)))
                    (submodules (resolve-module mod-name #f)))))
    (list (cons "modules" subs)
          (cons "procs" (car elts))
          (cons "syntax" (cadr elts))
          (cons "vars" (caddr elts)))))

(define (classify-module-object name var elts)
  (let ((obj (and (variable-bound? var)
                  (variable-ref var))))
    (cond ((or (not obj) (module? obj)) elts)
          ((or (procedure? obj) (program? obj))
           (list (cons (list name `("signature" . ,(obj-signature name obj)))
                       (car elts))
                 (cadr elts)
                 (caddr elts)))
          ((macro? obj)
           (list (car elts)
                 (cons (list name `("signature" . ,(obj-signature name obj)))
                       (cadr elts))
                 (caddr elts)))
          (else (list (car elts)
                      (cadr elts)
                      (cons (list name) (caddr elts)))))))
