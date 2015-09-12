;;; proof-auxmodes.el --- Arrange for auxiliary modes to be loaded when required
;;
;; Copyright (C) 2008, 2010 David Aspinall / LFCS Edinburgh
;; Author:    David Aspinall <David.Aspinall@ed.ac.uk>
;; License:   GPL (GNU GENERAL PUBLIC LICENSE)

;;; Commentary:
;;
;; Startup code from auxiliary modes are collected here, allowing late
;; loading of their main defining files and the possibility to disable them.
;;

(require 'proof-utils)			; proof-ass, proof-eval...

;;; Code:

;;
;; MMM
;;
(defun proof-mmm-support-available ()
  "A test to see whether mmm support is available."
  (and
   (or (featurep 'mmm-auto)
       (progn
	 ;; put bundled version on load path
	 (proof-add-to-load-path 
		(concat proof-home-directory "contrib/mmm/"))
	 ;; *should* always succeed unless bundled version broken
	 (proof-try-require 'mmm-auto)))
   ;; Load prover-specific config in <foo>-mmm.el
   (proof-try-require (proof-ass-sym mmm))))

(proof-eval-when-ready-for-assistant
    (if (and (proof-ass mmm-enable)
	     (proof-mmm-support-available))
	(proof-mmm-set-global t)))


;;
;; Maths menu
;;
(defun proof-maths-menu-support-available ()
  "A test to see whether maths-menu support is available.
The test loads optional prover-specific config in <foo>-maths-menu.el"
  (or (proof-try-require (proof-ass-sym maths-menu)) t))

(proof-eval-when-ready-for-assistant
    (if (and (proof-ass maths-menu-enable)
	     (proof-maths-menu-support-available))
	(proof-maths-menu-set-global t)))


;;
;; Unicode tokens
;;
(defun proof-unicode-tokens-support-available ()
  "A test to see whether unicode tokens support is available."
  ;; Requires prover-specific config in <foo>-unicode-tokens.el
  ;; Loaded before unicode-tokens.el to allow load-time config there
  (proof-try-require (proof-ass-sym unicode-tokens)))

(proof-eval-when-ready-for-assistant
    (if (and (proof-ass unicode-tokens-enable)
	     (proof-unicode-tokens-support-available))
	(proof-unicode-tokens-set-global t)))


(provide 'proof-auxmodes)

;;; proof-auxmodes.el ends here
