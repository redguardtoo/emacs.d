#lang racket/base

(require racket/list
         racket/function
         racket/path) ;explode-path NOT in racket/base prior to 6.0

;; A few functions we need that were added in Racket 6.0. This lets us
;; run on Racket 5.3.5 (perhaps earlier, but I haven't tested).
(provide find-collects-dir
         path->collects-relative
         current-directory-for-user
         hash-clear!)

;;; General note: Can use dynamic-require fail-thunk when we're sure
;;; the module exists, e.g. looking for a function in racket/base. But
;;; dynamic-require on a module that does not exist will cause an
;;; exception. So use exception handling when looking for things in
;;; collections introduced in a newer version of Racket.

(module+ test
  (require rackunit))

(define (our-find-collects-dir)
  (apply build-path
         (reverse (cdr (reverse (explode-path (collection-path "racket")))))))

(define find-collects-dir
  (dynamic-require 'setup/dirs 'find-collects-dir
                   (const our-find-collects-dir)))

(module+ test
  (check-not-exn (λ () (find-collects-dir))))

;; Warning: This is only the subset of path->collects-relative
;; functionality that we actually use.
(define (our-path->collects-relative path)
  (define cs (explode-path (find-collects-dir)))
  (define ps (explode-path (simplify-path path)))
  (cond [(> (length ps) (length cs))
         (define-values (as bs) (split-at ps (length cs)))
         (cond [(equal? as cs)
                (cons 'collects (map (compose string->bytes/utf-8
                                              path-element->string)
                                     bs))]
               [else path])]
        [else path]))

(define path->collects-relative
  (dynamic-require 'setup/collects 'path->collects-relative
                   (const our-path->collects-relative)))

(module+ test
  (check-equal? (path->collects-relative
                 (apply build-path (append (explode-path (find-collects-dir))
                                           (explode-path "racket/base"))))
                '(collects #"racket" #"base")))

;; This is a no-op, but that suffices for our use here because we only
;; use it in 6.0+ to revert back to pre-6.0 behavior.
(define our-current-directory-for-user (make-parameter #f))

(define current-directory-for-user
  (dynamic-require 'racket/base 'current-directory-for-user
                   (const our-current-directory-for-user)))

(module+ test
  (check-not-exn (λ () (current-directory-for-user))))

;;; Racket 6.0 adds hash-clear!

(define (our-hash-clear! ht)
  (for ([key (in-list (hash-keys ht))])
    (hash-remove! ht key)))

(module+ test
  (define ht (make-hash '((0 . "zero") (1 . "one") (2 . "two"))))
  (our-hash-clear! ht)
  (check-true (zero? (hash-count ht))))

(define hash-clear!
  (dynamic-require 'racket/base 'hash-clear!
                   (const our-hash-clear!)))

;; Local Variables:
;; coding: utf-8
;; comment-column: 40
;; indent-tabs-mode: nil
;; require-final-newline: t
;; show-trailing-whitespace: t
;; End:
