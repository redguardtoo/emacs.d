;;; modules.rkt -- module metadata

;; Copyright (C) 2009, 2010, 2011, 2012, 2013 Jose Antonio Ortega Ruiz

;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the Modified BSD License. You should
;; have received a copy of the license along with this program. If
;; not, see <http://www.xfree86.org/3.3.6/COPYRIGHT2.html#5>.

;; Start date: Wed May 06, 2009 02:35

#lang racket

(provide load-module
         ensure-module-spec
         module-spec->namespace
	 namespace->module-name
         namespace->module-path-name
         module-path-name->name
         module-spec->path-name
         module-path-index->name
         module-identifiers
         module-list
         submodules)

(require srfi/13
         syntax/modcode
         syntax/modresolve
         geiser/enter)

(define (ensure-module-spec spec)
  (cond [(symbol? spec) spec]
        [(not (string? spec)) #f]
        [else `(file ,spec)]))

(define (module-spec->namespace spec (lang #f) (current #t))
  (define (try-lang)
    (and lang
         (with-handlers ([exn? (const #f)])
           (load-module lang #f (current-namespace))
           (module->namespace lang))))
  (or (get-namespace spec)
      (try-lang)
      (and current (current-namespace))))

(define nowhere (open-output-nowhere))

(define (load-module spec (port #f) (ns #f))
  (parameterize ([current-error-port (or port nowhere)])
    (visit-module (ensure-module-spec spec))
    (when (namespace? ns)
      (current-namespace ns))))

(define (namespace->rmp ns)
  (with-handlers ([exn? (const #f)])
    (variable-reference->resolved-module-path
     (eval '(#%variable-reference) (or ns (current-namespace))))))

(define (namespace->module-path-name ns (p #f))
  (let ([rmp (namespace->rmp ns)])
    (or (and (resolved-module-path? rmp)
             (resolved-module-path-name rmp))
        p)))

(define (module-spec->path-name spec)
  (and (symbol? spec)
       (or (get-path spec)
           (register-path spec
                          (namespace->module-path-name
                           (module-spec->namespace spec #f #f))))))

(define unknown-module-name "*unresolved module*")

(define (unix-path->string path)
  (regexp-replace* "\\\\" (path->string path) "/"))

(define (path->name path)
  (if (path-string? path)
      (let* ([cpaths (map (compose unix-path->string path->directory-path)
                          (current-library-collection-paths))]
             [prefix-len (lambda (p)
                           (let ((pl (string-length p)))
                             (if (= pl (string-prefix-length p path))
                                 pl
                                 0)))]
             [lens (map prefix-len cpaths)]
             [real-path (substring path (apply max lens))])
        (if (absolute-path? real-path)
            (let-values ([(_ base __) (split-path path)])
              (unix-path->string base))
            (regexp-replace "\\.[^./]*$" real-path "")))
      path))

(define (module-path-name->name path)
  (cond [(path? path) (module-path-name->name (unix-path->string path))]
        ;; [(eq? path '#%kernel) "(kernel)"]
        [(path-string? path) (path->name path)]
        [(symbol? path) (symbol->string path)]
        [(list? path) (string-join (map (compose path->name ~a) path) "/")]
        [else (~a path)]))

(define (module-path-index->name mpi)
  (let ([rmp (module-path-index-resolve mpi)])
    (if (resolved-module-path? rmp)
        (module-path-name->name (resolved-module-path-name rmp))
        unknown-module-name)))

(define (namespace->module-name ns (p #f))
  (module-path-name->name (namespace->module-path-name ns p)))

(define (module-identifiers mod)
  (define (extract-ids ls)
    (append-map (lambda (idls)
                  (map car (cdr idls)))
                ls))
  (let-values ([(reg syn)
                (module-compiled-exports
                 (get-module-code (resolve-module-path
                                   (ensure-module-spec mod) #f)))])
    (values (extract-ids reg) (extract-ids syn))))

(define (skippable-dir? path)
  (call-with-values (lambda () (split-path path))
    (lambda (_ basename __)
      (member (path->string basename) '(".svn" "compiled")))))

(define path->symbol (compose string->symbol unix-path->string))

(define (path->entry path)
  (let ([ext (filename-extension path)])
    (and ext
         (or (bytes=? ext #"rkt") (bytes=? ext #"ss"))
         (not (bytes=? (bytes-append #"main" ext) (path->bytes path)))
         (let* ([path (unix-path->string path)]
                [len (- (string-length path) (bytes-length ext) 1)])
           (substring path 0 len)))))

(define (ensure-path datum)
  (if (string? datum)
      (string->path datum)
      datum))

(define main-rkt (build-path "main.rkt"))
(define main-ss (build-path "main.ss"))

(define ((visit-module-path reg?) path kind acc)
  (define (register e p)
    (when reg?
      (register-path (string->symbol e) (build-path (current-directory) p)))
    (values (cons e acc) reg?))
  (define (get-main path main)
    (and (file-exists? main) (build-path path main)))
  (define (find-main path)
    (parameterize ([current-directory path])
      (or (get-main path main-rkt) (get-main path main-ss))))
  (case kind
    [(file) (let ([entry (path->entry path)])
              (if (not entry) acc (register entry path)))]
    [(dir) (cond [(skippable-dir? path) (values acc #f)]
                 [(find-main path) => (curry register (unix-path->string path))]
                 [else (values acc reg?)])]
    [else acc]))

(define ((find-modules reg?) path acc)
  (if (directory-exists? path)
      (parameterize ([current-directory path])
        (fold-files (visit-module-path reg?) acc))
      acc))

(define (take-while pred lst)
  (let loop ([lst lst] [acc '()])
    (cond [(null? lst) (reverse acc)]
          [(pred (car lst)) (loop (cdr lst) (cons (car lst) acc))]
          [else (reverse acc)])))

(define (submodules mod)
  (let* ([mod-name (if (symbol? mod) mod (get-mod mod))]
         [mod-str (and (symbol? mod-name) (symbol->string mod-name))])
    (if mod-str
        (let ([ms (member mod-str (module-list))])
          (and ms
               (take-while (lambda (m) (string-prefix? mod-str m))
                           (cdr ms))))
        (find-submodules mod))))

(define (find-submodules path)
  (and (path-string? path)
       (let-values ([(dir base ign) (split-path path)])
         (and (or (equal? base main-rkt)
                  (equal? base main-ss))
              (map (lambda (m) (unix-path->string (build-path dir m)))
                   (remove "main" ((find-modules #f) dir '())))))))

(define (known-modules)
  (sort (foldl (find-modules #t)
               '()
               (current-library-collection-paths))
        string<?))

(define registered (make-hash))
(define registered-paths (make-hash))

(define (get-path mod)
  (hash-ref registered mod #f))

(define (get-mod path)
  (hash-ref registered-paths path #f))

(define (register-path mod path)
  (hash-set! registered mod path)
  (hash-set! registered-paths path mod)
  path)

(define module-cache #f)

(define (update-module-cache)
  (when (not module-cache) (set! module-cache (known-modules))))

(define (module-list)
  (update-module-cache)
  module-cache)

(define (startup)
 (thread update-module-cache)
 (void))

(startup)
