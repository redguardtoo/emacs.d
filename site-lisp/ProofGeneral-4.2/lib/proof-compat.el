;; proof-compat.el   Operating system and Emacs version compatibility
;;
;; Copyright (C) 2000-2010 LFCS Edinburgh.
;; Author:      David Aspinall <David.Aspinall@ed.ac.uk> and others
;; License:     GPL (GNU GENERAL PUBLIC LICENSE)
;;
;; proof-compat.el,v 12.1 2012/09/02 21:55:42 da Exp
;;
;; This file collects together compatibility hacks for different
;; operating systems and Emacs versions.  This is to help keep
;; track of them.
;;
;; The development policy for Proof General (since v3.7) is for the
;; main codebase to be written for the latest stable version of
;; GNU Emacs, following GNU Emacs advice on obsolete function calls.
;;
;; Since Proof General 4.0, XEmacs is not supported at all.
;;

(eval-when-compile
  (require 'easymenu))

(require 'cl)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Architecture flags
;;;

;; can use eval-and-compile to allow optimisation, but that would
;; require recompilation for Windows
(defvar proof-running-on-win32 (memq system-type '(win32 windows-nt cygwin))
  "Non-nil if Proof General is running on a windows variant system.")


;; Workaround a small bug in Carbon Emacs Winter 2008 (at least)
;; Menu presses query this variable, but it's not bound unless
;; mode engaged.  Not noticeable in normal use, but it is as soon
;; as debug-on-error is engaged.
(with-no-warnings
  (if (and (boundp 'carbon-emacs-package-version)
	   (not (boundp 'mac-key-mode)))
      (setq mac-key-mode nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Modifications and adjustments
;;;

;; Remove a custom setting.  Needed to support dynamic reconfiguration.
;; (We'd prefer that repeated defcustom calls acted like repeated
;;  "defvar treated as defconst" in XEmacs)
(defun pg-custom-undeclare-variable (symbol)
  "Remove a custom setting SYMBOL.
Done by removing all properties mentioned by custom library.
The symbol itself is left defined, in case it has been changed
in the current Emacs session."
  (mapc (lambda (prop) (remprop symbol prop))
	  '(default
	     standard-value
	     force-value
	     variable-comment
	     saved-variable-comment
	     variable-documentation
	     group-documentation
	     custom-set
	     custom-get
	     custom-options
	     custom-requests
	     custom-group
	     custom-prefix
	     custom-tag
	     custom-links
	     custom-version
	     saved-value
	     theme-value
	     theme-face)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; GNU Emacs compatibility with XEmacs
;;;

(unless (fboundp 'save-selected-frame)
(defmacro save-selected-frame (&rest body)
  "Execute forms in BODY, then restore the selected frame.
The value returned is the value of the last form in BODY."
  (let ((old-frame (gensym "ssf")))
    `(let ((,old-frame (selected-frame)))
       (unwind-protect
	   (progn ,@body)
	 (select-frame ,old-frame))))))

;; These functions are used in the intricate logic around
;; shrink-to-fit.

;; window-leftmost-p, window-rightmost-p: my implementations
(or (fboundp 'window-leftmost-p)
    (defun window-leftmost-p (window)
      (zerop (car (window-edges window)))))

(or (fboundp 'window-rightmost-p)
    (defun window-rightmost-p (window)
      (>= (nth 2 (window-edges window))
	  (frame-width (window-frame window)))))

(or (fboundp 'window-bottom-p)
    (defun window-bottom-p (window)
      (>= (nth 3 (window-edges window))
	  (frame-height (window-frame window)))))

;; find-coding-system emulation for GNU Emacs
(unless (fboundp 'find-coding-system)
  (defun find-coding-system (name)
    "Retrieve the coding system of the given name, or nil if non-such."
    (condition-case nil
	(check-coding-system name)
      (error nil))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; A naughty hack to completion.el
;;
;; At the moment IMO completion too eagerly adds stuff to
;; its database: the completion-before-command function
;; makes every suffix be added as a completion!

(eval-after-load "completion"
'(defun completion-before-command ()
  (if (and (symbolp this-command) (get this-command 'completion-function))
	(funcall (get this-command 'completion-function)))))


;; End of proof-compat.el
(provide 'proof-compat)
