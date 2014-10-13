;;; proof.el --- Proof General theorem prover interface.
;;
;; Copyright (C) 1998-2009 LFCS Edinburgh.
;; Authors:   David Aspinall, Yves Bertot, Healfdene Goguen,
;;            Thomas Kleymann and Dilip Sequeira
;; License:   GPL (GNU GENERAL PUBLIC LICENSE)
;;
;; Keywords: languages
;;
;; proof.el,v 12.1 2012/01/03 09:36:05 tews Exp
;;
;;; Commentary:
;;
;; This file loads Proof General.  It is required by the
;; individual prover modes.  Loading order of PG is:
;;
;; 1. proof-site (variables, autoloads & stubs for mode functions)
;; 2. stub <PA>-mode function sets proof-assistant-symbol and related variables
;; 3. prover-dependent variables defined in pg-custom
;; 4. stub explicitly loads <PA>/<PA>.el and execute real mode function
;; 5. <PA>.el requires this file, rest of PG loaded here
;; 6. further modules loaded by autoloads/prover-specific requires.
;;
;;
;;; Code:

(require 'proof-site)			; site/prover config, global vars, autoloads

(unless noninteractive
  (proof-splash-message))		; welcome the user now.

(require 'proof-compat)			; Emacs and OS compatibility
(require 'proof-utils)			; utilities
(require 'proof-config)			; configuration variables
(require 'proof-auxmodes)		; auxmode functions
(require 'proof-script)			; script mode
(require 'proof-tree)			; proof tree visualization with prooftree
(require 'proof-shell)			; shell mode

(provide 'proof)
;;; proof.el ends here
