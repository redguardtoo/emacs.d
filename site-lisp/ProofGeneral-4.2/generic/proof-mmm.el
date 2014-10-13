;; proof-mmm.el --- Support for MMM mode package
;;
;; Copyright (C) 2003, 2010 LFCS Edinburgh / David Aspinall
;; Author:    David Aspinall <David.Aspinall@ed.ac.uk>
;; License:   GPL (GNU GENERAL PUBLIC LICENSE)
;;
;; The MMM package is at http://mmm-mode.sourceforge.net/
;;
;; proof-mmm.el,v 12.0 2011/10/13 10:54:49 da Exp
;;
;;; Commentary:
;; 
;; Configuration for the prover is expected to reside in <foo>-mmm.el
;; It should define an MMM submode class called <foo>.
;;
;; NB: mmm-mode is bundled with Proof General, and PG will select
;; it's own version before any other version on the Emacs load path.
;; If you want to override this, simply load your version before
;; starting Emacs, with (require 'mmm-auto).
;;
;; Credits: thanks to Stefan Monnier for pointing me to this package,
;; and Michael Abraham Shulman for providing it.
;;



;;; Code:
(eval-when-compile
  (require 'cl))

(eval-when (compile)
  (require 'proof-auxmodes)	  ; will be loaded
  (require 'mmm-auto))		  ; loaded dynamically by proof-auxmodes

;; The following function is called by the menu item for MMM-Mode.  It
;; is an attempt at an intuitive behaviour without confusing the user
;; with extra "in this buffer" and "everywhere" options.  We make the
;; global option track the last setting made for any buffer.  The menu
;; toggle displays the status of the buffer (as seen in the modeline)
;; rather than the PG setting.

;;;###autoload
(defun proof-mmm-set-global (flag)
  "Set global status of MMM mode for PG buffers to be FLAG."
  (let ((automode-entry (list (proof-ass-sym mode) nil
			      proof-assistant-symbol)))
    (if flag
	(add-to-list 'mmm-mode-ext-classes-alist
		     automode-entry)
      (setq mmm-mode-ext-classes-alist
	    (delete automode-entry
		    mmm-mode-ext-classes-alist)))
    ;; make sure MMM obeys the mmm-mode-ext-classes-alist
    (unless (eq mmm-global-mode t)
      (setq mmm-global-mode 'pg-use-mode-ext-classes-alist))))

;;;###autoload
(defun proof-mmm-enable ()
  "Turn on or off MMM mode in Proof General script buffer.
This invokes `mmm-mode' to toggle the setting for the current
buffer, and then sets PG's option for default to match.
Also we arrange to have MMM mode turn itself on automatically
in future if we have just activated it for this buffer."
  (interactive)
  (when (proof-mmm-support-available)
    ;; Make sure auto mode follows PG's global setting. (NB: might do
    ;; only if global state changes, but by now (proof-ass mmm-mode) set).
    (with-no-warnings ; bytecomp gives spurious error
		      ; "proof-mmm-set-global might not be defined"
		      ; because the autoload overrides the definition above(!)
      (proof-mmm-set-global (not mmm-mode)))
    (mmm-mode)))

(provide 'proof-mmm)

;;; proof-mmm.el ends here
