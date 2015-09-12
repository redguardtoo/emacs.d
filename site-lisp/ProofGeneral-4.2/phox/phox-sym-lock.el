;; phox-sym-lock.el --- Extension of Font-Lock mode for symbol fontification.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;        Copyright © 1997-1998 Albert Cohen, all rights reserved.
;;         Copying is covered by the GNU General Public License.
;;
;;    This program is free software; you can redistribute it and/or modify
;;    it under the terms of the GNU General Public License as published by
;;    the Free Software Foundation; either version 2 of the License, or
;;    (at your option) any later version.
;;
;;    This program is distributed in the hope that it will be useful,
;;    but WITHOUT ANY WARRANTY; without even the implied warranty of
;;    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
;;    GNU General Public License for more details.

(require 'proof-compat)			; avoid compile warnings

(defcustom phox-sym-lock-enabled t
  "*Whether to use yum symbol or not."
  :type 'boolean
  :group 'phox)

;; DA: I have crudely hacked this file so that it compiles cleanly.
;; It won't work now, but I hope we can use Unicode Tokens instead.

(declare-function map-extents "nofile")
(declare-function extent-face "nofile")
(declare-function face-property "nofile")
(declare-function set-extent-endpoints "nofile")
(declare-function extent-start-position "nofile")
(declare-function extent-end-position "nofile")
(declare-function set-extent-property "nofile")
(declare-function face-font-name "nofile")
(declare-function font-name "nofile")
(declare-function char-int "nofile")
(declare-function obj "nofile")
(declare-function set-face-property "nofile")
(declare-function add-menu-button "nofile")


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                                 History
;;
;; first prototype by wg <wg@cs.tu-berlin.de> 5-96
;; tweaked by Steve Dunham <dunham@gdl.msu.edu> 5-96
;; rewritten and enhanced by Albert Cohen <Albert.Cohen@prism.uvsq.fr> 3-97
;; new symbol-face format and ergonomy improvement by Albert Cohen 2-98
;; major step towards portability and customization by Albert Cohen 5-98
;; removed bug with multiple appends in hook by Albert Cohen 3-99
;; removed phox-sym-lock-face&atom which where not working by C Raffalli 4-2000

;; more about symbol font ? check out: xfd -fn '-adobe-symbol-*--12-*'

(require 'font-lock)
(if (featurep 'xemacs)
    (require 'atomic-extents))  ;; not available on GNU Emacs

(defvar phox-sym-lock-sym-count 0
  "Counter for internal symbols.")

(defvar phox-sym-lock-ext-start nil "Temporary for atomicization.")
(make-variable-buffer-local 'phox-sym-lock-ext-start)
(defvar phox-sym-lock-ext-end nil "Temporary for atomicization.")
(make-variable-buffer-local 'phox-sym-lock-ext-end)

(defvar phox-sym-lock-font-size nil
  "Default size for Phox-Sym-Lock symbol font.")
(make-variable-buffer-local 'phox-sym-lock-font-size)
(put 'phox-sym-lock-font-size 'permanent-local t)

(defvar phox-sym-lock-keywords nil
  "Similar to `font-lock-keywords'.")
(make-variable-buffer-local 'phox-sym-lock-keywords)
(put 'phox-sym-lock-keywords 'permanent-local t)

(defvar phox-sym-lock-enabled nil
  "Phox-Sym-Lock switch.")
(make-variable-buffer-local 'phox-sym-lock-enabled)
(put 'phox-sym-lock-enabled 'permanent-local t)

(defvar phox-sym-lock-color (face-foreground 'default)
  "*Phox-Sym-Lock default color in `font-lock-use-colors' mode.")
(make-variable-buffer-local 'phox-sym-lock-color)
(put 'phox-sym-lock-color 'permanent-local t)

(defvar phox-sym-lock-mouse-face 'default
  "*Face for symbols when under mouse.")
(make-variable-buffer-local 'phox-sym-lock-mouse-face)
(put 'phox-sym-lock-mouse-face 'permanent-local t)

(defvar phox-sym-lock-mouse-face-enabled t
  "Mouse face switch.")
(make-variable-buffer-local 'phox-sym-lock-mouse-face-enabled)
(put 'phox-sym-lock-mouse-face-enabled 'permanent-local t)

(defconst phox-sym-lock-with-mule (featurep 'mule)
  "Are we using Mule Xemacs ?")

(defun phox-sym-lock-gen-symbol (&optional prefix)
  "Generate a new internal symbol."
  ;; where is the standard function to do this ?
  (setq phox-sym-lock-sym-count (+ phox-sym-lock-sym-count 1))
  (intern (concat "phox-sym-lock-gen-" (or prefix "")
		  (int-to-string phox-sym-lock-sym-count))))


(defun phox-sym-lock-make-symbols-atomic (&optional begin end)
  "Function to make symbol faces atomic."
  (if phox-sym-lock-enabled
      (map-extents
       (lambda (extent maparg)
	 (let ((face (extent-face extent)) (ext))
	   (if (and face (setq ext (face-property face 'phox-sym-lock-remap)))
	       (progn
		 (if (numberp ext)
		     (set-extent-endpoints
		      extent (- (extent-start-position extent) ext)
		      (extent-end-position extent)))
		 (if ext
		     (progn
		       (if phox-sym-lock-mouse-face-enabled
			   (set-extent-property extent 'mouse-face
						phox-sym-lock-mouse-face))
		       (set-extent-property extent 'atomic t)
		       (set-extent-property extent 'start-open t))))))
	 nil)
       (current-buffer)
       (if begin (save-excursion (goto-char begin) (beginning-of-line) (point))
	 (point-min))
       (if end (save-excursion (goto-char end) (end-of-line) (point))
	 (point-max))
       nil nil)))

(defun phox-sym-lock-compute-font-size ()
  "Computes the size of the \"better\" symbol font."
  (let ((font-reg (if proof-running-on-win32
		      "[^:]*:[^:]*:\\([^:]*\\):[^:]*:[^:]*"
		    "-[^-]*-[^-]*-[^-]*-[^-]*-[^-]*-[^-]*-\\([^-]*\\)-.*"))
	(font-pat (if proof-running-on-win32
		      "Symbol:Regular:*::Symbol"
		      "-adobe-symbol-medium-r-normal--*")))
    (let (
;       face-height is not very good on win32. Why ?
	  (num (if (and (not proof-running-on-win32) (fboundp 'face-height))
		   (face-height 'default)
		 (let ((str (face-font-name 'default)))
		   (if
		       (string-match font-reg str)
		       (string-to-number (substring str (match-beginning 1)
						    (match-end 1)))))))
	  (maxsize 100) (size) (oldsize)
	  (lf (and (fboundp 'list-fonts) ; da: what is this function? not defined
		   (list-fonts font-pat))))
    (while (and lf maxsize)
      (if
	  (string-match font-reg
		    (car lf))
	  (let ((str-size (substring (car lf) (match-beginning 1)
						    (match-end 1))))
	    ; test for variable size fonts. Hope it is generic ?
	    (if (or (equal str-size "*")(equal str-size ""))
		(progn
		  (setq oldsize num)
		  (setq lf nil))
	      (setq size (string-to-number str-size))
	      (if (and (> size num) (< size maxsize))
		  (setq lf nil)
		(setq oldsize size)))))
      (setq lf (cdr lf)))
    (number-to-string (if (and oldsize (< oldsize maxsize)) oldsize num)))))

(defvar phox-sym-lock-font-name
  (if window-system
      (if proof-running-on-win32
	  (concat "Symbol:Regular:"
		  (if phox-sym-lock-font-size phox-sym-lock-font-size
		    (phox-sym-lock-compute-font-size))
		"::Symbol")
	(concat "-adobe-symbol-medium-r-normal--"
		(if phox-sym-lock-font-size phox-sym-lock-font-size
		  (phox-sym-lock-compute-font-size))
		"-*-*-*-p-*-adobe-fontspecific"))
    "")
  "Name of the font used by Phox-Sym-Lock.")
(make-variable-buffer-local 'phox-sym-lock-font-name)
(put 'phox-sym-lock-font-name 'permanent-local t)

(make-face 'phox-sym-lock-adobe-symbol-face)
;  DA: DISABLED THIS top level form (PG 4.0) 
;; (if phox-sym-lock-with-mule 
;;     (progn
;;       (make-charset 'phox-sym-lock-cset-left "Char set for symbol font"
;; 		    (list 'registry "adobe-fontspecific"
;; 			  'dimension 1
;; 			  'chars 94
;; ;;			  'final 53
;; ;; DA PG 3.7: above line doesn't work on XEmacs 21.5b28, gives
;; ;; Character set already defined for this DIMENSION/CHARS/FINAL/DIRECTION combo (indian-is13194)
;; ;; DA: Will 55 work?
;; 			  'final 55
;; 			  'graphic 0))
;;       (make-charset 'phox-sym-lock-cset-right "Char set for symbol font"
;; 		    (list 'registry "adobe-fontspecific"
;; 			  'dimension 1
;; 			  'chars 94
;; 			  'final 54
;; 			  'graphic 1))
;;       (set-face-property 'phox-sym-lock-adobe-symbol-face
;; 			 'font phox-sym-lock-font-name nil
;; 			 ;; DA: removed next line, it breaks "make magic" in doc
;; 			 ;; '(mule-fonts) 'prepend,
;; 			 ))
;;   (set-face-font 'phox-sym-lock-adobe-symbol-face phox-sym-lock-font-name 'global))

(defun phox-sym-lock-set-foreground ()
  "Set foreground color of Phox-Sym-Lock faces."
  (if (and (boundp 'phox-sym-lock-defaults) phox-sym-lock-defaults)
      (let ((l (car phox-sym-lock-defaults))
	    (color (if (and (boundp 'font-lock-use-fonts) font-lock-use-fonts)
		       (face-foreground 'default) phox-sym-lock-color)))
	(if (and (consp l) (eq (car l) 'quote)) (setq l (eval l)))
	(if (symbolp l) (setq l (eval l)))
	(dolist (c l)
	  (setq c (nth 2 c))
	  (if (consp c) (setq c (eval c)))
	  (if (string-match "-adobe-symbol-" (font-name (face-font c)))
	      (set-face-foreground c color))))))

(defun phox-sym-lock-translate-char (char)
  (if phox-sym-lock-with-mule
      (let ((code (if (integerp char) char (char-int char))))
	(with-no-warnings ;; da: dynamic scope obj
	  (if (< code 128)
	      (make-char 'phox-sym-lock-cset-left obj)
	    (make-char 'phox-sym-lock-cset-right (- obj 128)))))
    char))

(defun phox-sym-lock-translate-char-or-string (obj)
  (if (stringp obj)
    (if phox-sym-lock-with-mule
	(concat (mapcar 'phox-sym-lock-translate-char obj))
      (obj))
    (make-string 1 (phox-sym-lock-translate-char obj))))

(defun phox-sym-lock-remap-face (pat pos obj atomic)
  "Make a temporary face which remaps the POS char of PAT to the
given OBJ under `phox-sym-lock-adobe-symbol-face' and all other characters to
the empty string. OBJ may either be a string or a character."
  (let* ((name (phox-sym-lock-gen-symbol "face"))
	 (table (make-display-table))
	 (tface (make-face name "phox-sym-lock-remap-face")))
    (fillarray table "")
    (aset table (string-to-char (substring pat (1- pos) pos))
	  (phox-sym-lock-translate-char-or-string obj))
    (set-face-foreground tface (if (and (boundp 'font-lock-use-fonts)
					font-lock-use-fonts)
				   (face-foreground 'default) phox-sym-lock-color))
    (set-face-property tface 'display-table table)
    (set-face-property tface 'font (face-font 'phox-sym-lock-adobe-symbol-face))
    (set-face-property tface 'phox-sym-lock-remap atomic) ; mark it
    tface  ; return face value and not face name
	   ; the temporary face would be otherwise GCed
    ))

(defvar phox-sym-lock-clear-face
  (let* ((name (phox-sym-lock-gen-symbol "face"))
	 (table (make-display-table))
	 (tface (make-face name "phox-sym-lock-remap-face")))
    (fillarray table "")
    (set-face-property tface 'display-table table)
    (set-face-property tface 'phox-sym-lock-remap 1) ; mark it
    tface
    ;; return face value and not face name
    ;; the temporary face would be otherwise GCed
    ))

(defun phox-sym-lock (fl)
  "Create font-lock table entries from a list of (PAT NUM POS OBJ) where
PAT (at NUM) is substituted by OBJ under `phox-sym-lock-adobe-symbol-face'. The
face's extent will become atomic."
  (message "Computing Phox-Sym-Lock faces...")
  (setq phox-sym-lock-keywords (phox-sym-lock-rec fl))
  (setq phox-sym-lock-enabled t)
  (message "Computing Phox-Sym-Lock faces... done."))

(defun phox-sym-lock-rec (fl)
  (let ((f (car fl)))
    (if f
	(cons (apply 'phox-sym-lock-atom-face f)
	      (phox-sym-lock-rec (cdr fl))))))

(defun phox-sym-lock-atom-face (pat num pos obj &optional override)
  "Define an entry for the font-lock table which substitutes PAT (at NUM) by
OBJ under `phox-sym-lock-adobe-symbol-face'. The face extent will become atomic."
  (list pat num (phox-sym-lock-remap-face pat pos obj t) override))

(defun phox-sym-lock-pre-idle-hook-first ()
  ;; da: XEmacs isms
  ;; (condition-case nil
  ;;     (if (and phox-sym-lock-enabled font-lock-old-extent)
  ;; 	  (setq phox-sym-lock-ext-start (extent-start-position font-lock-old-extent)
  ;; 		phox-sym-lock-ext-end (extent-end-position font-lock-old-extent))
  ;; 	(setq phox-sym-lock-ext-start nil))
  ;;   (error (setq phox-sym-lock-ext-start nil))))
)

(defun phox-sym-lock-pre-idle-hook-last ()
  (condition-case nil
      (if (and phox-sym-lock-enabled phox-sym-lock-ext-start)
	  (phox-sym-lock-make-symbols-atomic phox-sym-lock-ext-start phox-sym-lock-ext-end))
    (error (warn "Error caught in `phox-sym-lock-pre-idle-hook-last'"))))

(add-hook 'font-lock-after-fontify-buffer-hook
	  'phox-sym-lock-make-symbols-atomic)

(defun phox-sym-lock-enable ()
  "Enable Phox-Sym-Lock on this buffer."
  (interactive)
  (if (not phox-sym-lock-keywords)
      (error "No Phox-Sym-Lock keywords defined!")
    (setq phox-sym-lock-enabled t)
    (if font-lock-mode
	(progn
;	  (setq font-lock-keywords nil) ; Font-Lock explicit-defaults bug!
	  (font-lock-set-defaults)
	  (font-lock-fontify-buffer)))
    (message "Phox-Sym-Lock enabled.")))

(defun phox-sym-lock-disable ()
  "Disable Phox-Sym-Lock on this buffer."
  (interactive)
  (if (not phox-sym-lock-keywords)
      (error "No Phox-Sym-Lock keywords defined!")
    (setq phox-sym-lock-enabled nil)
    (if font-lock-mode
	(progn
;	  (setq font-lock-keywords nil) ; Font-Lock explicit-defaults bug!
	  (font-lock-set-defaults)
	  (font-lock-fontify-buffer)))
    (message "Phox-Sym-Lock disabled.")))

(defun phox-sym-lock-mouse-face-enable ()
  "Enable special face for symbols under mouse."
  (interactive)
  (setq phox-sym-lock-mouse-face-enabled t)
  (if phox-sym-lock-enabled
      (font-lock-fontify-buffer)))

(defun phox-sym-lock-mouse-face-disable ()
  "Disable special face for symbols under mouse."
  (interactive)
  (setq phox-sym-lock-mouse-face-enabled nil)
  (if phox-sym-lock-enabled
      (font-lock-fontify-buffer)))

(defun phox-sym-lock-font-lock-hook ()
  "Function called by `font-lock-mode' for initialization purposes."
  (add-hook 'pre-idle-hook 'phox-sym-lock-pre-idle-hook-first)
  (add-hook 'pre-idle-hook 'phox-sym-lock-pre-idle-hook-last t)
  (add-menu-button '("Options" "Syntax Highlighting")
		   ["Phox-Sym-Lock"
		    (if phox-sym-lock-enabled (phox-sym-lock-disable) (phox-sym-lock-enable))
		    :style toggle :selected phox-sym-lock-enabled
		    :active phox-sym-lock-keywords] "Automatic")
  (if (and (featurep 'phox-sym-lock) phox-sym-lock-enabled
	   font-lock-defaults (boundp 'phox-sym-lock-keywords))
      (progn
	(phox-sym-lock-patch-keywords)
	(phox-sym-lock-set-foreground))))

(defun font-lock-set-defaults (&optional explicit-defaults)
  (when
      (and
       (featurep 'font-lock)
       ;; da: font-lock has changed:
       ;; (if font-lock-auto-fontify
       ;; 	   (not (memq major-mode font-lock-mode-disable-list))
       ;; 	 (memq major-mode font-lock-mode-enable-list))
       ;; (font-lock-set-defaults-1 explicit-defaults)
       (phox-sym-lock-patch-keywords))
    (turn-on-font-lock)))

(defun phox-sym-lock-patch-keywords ()
  (if (and font-lock-keywords phox-sym-lock-enabled
	   (boundp 'phox-sym-lock-keywords)
	   (listp (car font-lock-keywords))
	   (listp (cdar font-lock-keywords))
	   (listp (cddar font-lock-keywords))
	   (or (listp (caddar font-lock-keywords))
	       (not (string-match
		     "phox-sym-lock"
		     (symbol-name
		      (face-name (cadr (cdar
					font-lock-keywords))))))))
      (setq font-lock-keywords (append phox-sym-lock-keywords
				       font-lock-keywords))) t)

(add-hook 'font-lock-mode-hook 'phox-sym-lock-font-lock-hook)

(provide 'phox-sym-lock)
