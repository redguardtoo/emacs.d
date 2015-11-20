#lang racket/base

(require "util.rkt")

(provide gui-required?
         require-gui
         txt/gui)

(define root-eventspace #f) ;#f until racket/gui/base required first time

(define (gui-required?)
  (not (not root-eventspace)))

;; This must be called from the main thread, under the main custodian!
(define (require-gui)
  (when (gui-required?)
    (error 'require-gui "Already required"))
  (display-commented "on-demand one-time instantiation of racket/gui/base")
  (define current-eventspace (gui-dyn-req 'current-eventspace))
  (define make-eventspace    (gui-dyn-req 'make-eventspace))
  (set! root-eventspace (make-eventspace))
  (current-eventspace root-eventspace))

;; Like mz/mr from racket/sandbox.
(define-syntax txt/gui
  (syntax-rules ()
    [(_ txtval guisym)
     (if (gui-required?)
         (gui-dyn-req 'guisym)
         txtval)]))

(define (gui-dyn-req sym)
  (dynamic-require 'racket/gui/base sym))

;; Local Variables:
;; coding: utf-8
;; comment-column: 40
;; indent-tabs-mode: nil
;; require-final-newline: t
;; show-trailing-whitespace: t
;; End:
