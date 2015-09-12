;;; proof-toolbar.el --- Toolbar for Proof General
;;
;; Copyright (C) 1998-2009  David Aspinall / LFCS.
;; Author:    David Aspinall <David.Aspinall@ed.ac.uk>
;; License:   GPL (GNU GENERAL PUBLIC LICENSE)
;;
;; proof-toolbar.el,v 12.3 2012/07/15 08:58:14 da Exp
;;
;;; Commentary:
;;
;; It's a little bit tricky to add prover-specific items:
;; presently it must be done before this file is loaded.
;; We could improve on that by generating everything on-thy-fly
;; in proof-toolbar-setup.
;;
;; See `proof-toolbar-entries-default' and `<PA>-toolbar-entries'
;; in pg-custom.el for the default generic toolbar and
;; the per-prover toolbar contents variable.
;;

;;; Code:

(eval-and-compile
  (require 'span)
  (require 'proof-utils)
  (require 'proof-config)
  (require 'tool-bar))			; needed for some emacsen without X


;;
;; Function, icon, button names
;;

(defun proof-toolbar-function (token)
  "Construct name of toolbar function for TOKEN."
  (intern (concat "proof-toolbar-" (symbol-name token))))

(defun proof-toolbar-icon (token)
  "Construct name of toolbar icon for TOKEN."
  (intern (concat "proof-toolbar-" (symbol-name token) "-icon")))

(defun proof-toolbar-enabler (token)
  "Construct name of toolbar enabler for TOKEN."
  (intern (concat "proof-toolbar-" (symbol-name token) "-enable-p")))


;;
;; Now the toolbar icons and buttons
;;

(defun proof-toolbar-make-icon (tle)
  "Make icon variable and icon list entry from a PA-toolbar-entries entry."
  (let* ((icon     (car tle))
	 (toolbarp (nth 3 tle))
	 (iconname (symbol-name icon))
	 (iconvar  (proof-toolbar-icon icon)))
    (when toolbarp
      (set iconvar (concat "epg-" iconname)))))

(defun proof-toolbar-make-toolbar-items (map tles)
  "Make toolbar button descriptors from a PA-toolbar-entries entry."
  ;; Entry format:  (TOKEN MENUNAME TOOLTIP TOOLBAR-P [VISIBLE-P])
  (dolist (tle tles)
    (let* ((token     (nth 0 tle))
	   (longtoken (intern (symbol-name token)))
	   (includep  (nth 3 tle))
	   (visiblep  (nth 4 tle))
	   (icon      (proof-toolbar-icon token))
	   (buttonfn  (proof-toolbar-function token))
	   (enabler   (proof-toolbar-enabler token))
	   (tooltip   (and includep (nth 2 tle)))
	   (props     (append
		       (list :help tooltip)
		       (if (fboundp enabler)
			   (list :enable (list enabler)))
		       (if visiblep
			   (list :visible visiblep)))))
      (if (eval includep)
	  (apply 'tool-bar-local-item
		 (eval icon) buttonfn longtoken map props)))))

;;
;; Code for displaying and refreshing toolbar
;;

(defvar proof-toolbar-map nil
  "Proof mode toolbar button list.  Set in `proof-toolbar-setup'.")

(defun proof-toolbar-available-p ()
  "Check if  toolbar support is available in this Emacs."
  (and
   window-system
   (featurep 'tool-bar)	                ;; GNU Emacs tool-bar library
   (or (image-type-available-p 'xpm)    ;; and XPM
       (image-type-available-p 'png)))) ;; or PNG


;;;###autoload
(defun proof-toolbar-setup ()
  "Initialize Proof General toolbar and enable it for all PG buffers.
If `proof-toolbar-enable' is nil, change the buffer toolbars
back the default toolbar."
  (interactive)
  (when (proof-toolbar-available-p)
    (unless proof-toolbar-map
      (setq proof-toolbar-map (make-sparse-keymap))
      (if (boundp 'image-load-path)
	  (add-to-list 'image-load-path proof-images-directory)) ; rude?
      (mapc 'proof-toolbar-make-icon (proof-ass toolbar-entries))
      (proof-toolbar-make-toolbar-items proof-toolbar-map
					(proof-ass toolbar-entries)))
    (proof-map-buffers
     (append
      (proof-buffers-in-mode proof-mode-for-script)
      (proof-associated-buffers))
     (when proof-toolbar-enable
       (set (make-local-variable 'tool-bar-map) proof-toolbar-map))
     (when (not proof-toolbar-enable)
       (kill-local-variable 'tool-bar-map)))))

(defun proof-toolbar-enable ()
  "Take action when the toolbar is enabled or disabled."
  (proof-toolbar-setup)
  (redraw-display))

;;;###autoload (autoload 'proof-toolbar-toggle "proof-toolbar")
(proof-deftoggle proof-toolbar-enable proof-toolbar-toggle)

;;
;;
;; Proof General Toolbar and Scripting Menu Functions
;; --------------------------------------------------
;;
;; Defaults functions are provided below for: up, down, restart
;; Code for specific provers may define the symbols below to use
;; the other buttons: next, prev, goal, qed (images are provided).
;;
;;  proof-toolbar-next		   next function
;;  proof-toolbar-next-enable      enable predicate for next
;;
;; If no -enable function is defined, button is always enabled.
;;
;; To add support for more buttons or alter the default
;; images, <PA>-toolbar-entries should be adjusted.
;; See proof-config.el for that.
;;
;; Note that since the toolbar is displayed for goals and response
;; buffers too, enablers and command functions must potentially switch
;; buffer first.
;;

;; Undo

(defalias 'proof-toolbar-undo 'proof-undo-last-successful-command)

(defun proof-toolbar-undo-enable-p ()
  (proof-with-script-buffer
   (and (proof-shell-available-p)
	(> (proof-unprocessed-begin) (point-min)))))

;; Delete

(defalias 'proof-toolbar-delete 'proof-undo-and-delete-last-successful-command)

(defun proof-toolbar-delete-enable-p ()
  (proof-with-script-buffer
   (and (not buffer-read-only)
	(proof-shell-available-p)
	(> (proof-unprocessed-begin) (point-min)))))

;; Home

(defalias 'proof-toolbar-home 'proof-goto-end-of-locked)

;; Next

(defalias 'proof-toolbar-next 'proof-assert-next-command-interactive)

(defun proof-toolbar-next-enable-p ()
  (proof-with-script-buffer
   (not (proof-locked-region-full-p))))

;; Goto

(defalias 'proof-toolbar-goto 'proof-goto-point)

(defun proof-toolbar-goto-enable-p ()
  (eq proof-buffer-type 'script))

;; Retract

(defalias 'proof-toolbar-retract 'proof-retract-buffer)

(defun proof-toolbar-retract-enable-p ()
  (proof-with-script-buffer
   (not (proof-locked-region-empty-p))))

;; Use

(defalias 'proof-toolbar-use 'proof-process-buffer)
(defalias 'proof-toolbar-use-enable-p 'proof-toolbar-next-enable-p)

;; Prooftree

(defalias 'proof-toolbar-prooftree 'proof-tree-external-display-toggle)

;; Restart

(defalias 'proof-toolbar-restart 'proof-shell-restart)

;; Goal

(defalias 'proof-toolbar-goal 'proof-issue-goal)

;; QED

(defalias 'proof-toolbar-qed 'proof-issue-save)

(defun proof-toolbar-qed-enable-p ()
  (proof-with-script-buffer
   (and proof-save-command
	proof-shell-proof-completed
	(proof-shell-available-p))))

;; State

(defalias 'proof-toolbar-state 'proof-prf)
(defalias 'proof-toolbar-state-enable-p 'proof-shell-available-p)

;; Context

(defalias 'proof-toolbar-context 'proof-ctxt)
(defalias 'proof-toolbar-context-enable-p 'proof-shell-available-p)

;; Command

(defalias 'proof-toolbar-command 'proof-minibuffer-cmd)
(defalias 'proof-toolbar-command-enable-p 'proof-shell-available-p)

;; Help  (I was an alias for this)

(defun proof-toolbar-help ()
  (interactive)
  (info "ProofGeneral"))

;; Find

(defalias 'proof-toolbar-find 'proof-find-theorems)
(defalias 'proof-toolbar-find-enable-p 'proof-shell-available-p)

;; Info

(defalias 'proof-toolbar-info 'proof-query-identifier)
(defalias 'proof-toolbar-info-enable-p 'proof-shell-available-p)

;; Visibility (not on toolbar)

(defalias 'proof-toolbar-visibility 'pg-toggle-visibility)

(defun proof-toolbar-visibility-enable-p ()
  (span-property-safe (span-at (point) 'type) 'idiom))

;; Interrupt

(defalias 'proof-toolbar-interrupt 'proof-interrupt-process)
(defun proof-toolbar-interrupt-enable-p () proof-shell-busy)

;;
;; Scripting Menu
;;

;; TODO: pass in map argument, don't use easymenu.
;;;###autoload
(defun proof-toolbar-scripting-menu ()
  "Menu made from the Proof General toolbar commands."
  (let (menu)
    (dolist (tle (proof-ass toolbar-entries))
      ;; Entry format:  (TOKEN MENUNAME TOOLTIP TOOLBAR-P VISIBLE-P)
      (let* ((token	(car tle))
	     (menuname  (cadr tle))
	     (tooltip   (nth 2 tle))
	     (visiblep  (nth 4 tle))
	     (enabler   (proof-toolbar-enabler token))
	     (fnname	(proof-toolbar-function token))
	     ;; fnval: remove defalias to get keybinding onto menu;
	     ;; NB: function and alias must both be defined for this
	     ;; to work!!
	     (fnval	  (if (symbolp (symbol-function fnname))
			      (symbol-function fnname)
			    fnname)))
	(when (and menuname (eval visiblep))
	  (setq menu
		(cons
		 (vconcat
		  (vector menuname fnval :help tooltip)
		  (if (fboundp enabler)
		      ;; NB: :active not :enable, for easymenu
		      (vector :active (list (proof-toolbar-enabler token))))
		  (if visiblep
		      (vector :visible visiblep)))
		 menu)))))
    (reverse menu)))


(provide 'proof-toolbar)

;;; proof-toolbar.el ends here
