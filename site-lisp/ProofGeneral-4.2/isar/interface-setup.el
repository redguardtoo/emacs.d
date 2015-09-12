;; interface-setup.el Interface wrapper for Isabelle Proof General
;;
;; This file is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 2, or (at your option)
;; any later version.
;;
;; Author: Markus Wenzel <wenzelm@in.tum.de>
;;
;; interface-setup.el,v 7.0 2002/08/29 09:14:03 da Exp
;;

;;
;; Tool bar
;;

(if (and window-system (fboundp 'tool-bar-mode)) (tool-bar-mode t))

;;
;; Unicode
;;

(let ((unicode (getenv "PROOFGENERAL_UNICODE")))
  (if (and unicode (not (equal unicode "")))
      (customize-set-variable 'proof-shell-unicode (equal unicode "true"))))

;;
;; Unicode symbols
;;

(let ((symbols (getenv "PROOFGENERAL_UNICODE_SYMBOLS")))
  (if (and symbols (not (equal symbols "")))
      (customize-set-variable 'isar-unicode-tokens-enable (equal symbols "true"))))

;;
;; Proof General startup
;;

(if (not (featurep 'proof-site))
    (load (concat (getenv "PROOFGENERAL_HOME") "/generic/proof-site.el")))
