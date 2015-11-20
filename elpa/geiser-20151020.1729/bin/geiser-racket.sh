#!/bin/bash
#|
topdir=$(dirname $0)
elpa_scheme=$topdir/scheme
in_scheme=$topdir/../scheme
top=$(if [ -d $elpa_scheme ]; then echo $elpa_scheme; else echo $in_scheme; fi)
exec racket -i -S "$top/racket" -l errortrace -cu "$0" ${1+"$@"}
|#

#lang racket/base

(require (lib "cmdline.rkt"))
(require geiser/server)

(define port (make-parameter 0))
(define host (make-parameter #f (lambda (h) (and (string? h) h))))

(command-line
 "run-racket.sh" (current-command-line-arguments)
 (once-each
  (("-n" "--hostname") n "Network hostname, or #f for all interfaces" (host n))
  (("-p" "--port") p "Geiser server port" (port (string->number p)))))

(printf "Geiser server running at port ~a~%" (start-geiser (port) (host)))
