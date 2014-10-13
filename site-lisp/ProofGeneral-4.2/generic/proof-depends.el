;;; proof-depends.el --- Theorem-theorem and theorem-definition dependencies
;;
;; Copyright (C) 2000-2004, 2010 University of Edinburgh.
;; Authors:      David Aspinall <David.Aspinall@ed.ac.uk>
;;	         Earlier version by Fiona McNeil.
;; License:      GPL (GNU GENERAL PUBLIC LICENSE)
;; Status:       Experimental code
;;
;; proof-depends.el,v 12.0 2011/10/13 10:54:49 da Exp
;;
;;; Commentary:
;; 
;; Based on Fiona McNeill's MSc project on analysing dependencies
;; within proofs.  Code rewritten by David Aspinall.
;;



(require 'cl)
(require 'span)
(require 'pg-vars)
(require 'proof-config)
(require 'proof-autoloads)

(defvar proof-thm-names-of-files nil
  "A list of file and theorems contained within.
A list of lists; the first element of each list is a file-name, the
second element a list of all the thm names in that file.
i.e.: ((file-name-1 (thm1 thm2 thm3)) (file-name-2 (thm1 thm2 thm3)))")

(defvar proof-def-names-of-files nil
  "A list of files and defs contained within.
A list of lists; the first element of each list is a file-name, the
second element a list of all the def names in that file.
i.e.: ((file-name-1 (def1 def2 def3)) (file-name-2 (def1 def2 def3)))")


;;; Code:

;; Utility functions

(defun proof-depends-module-name-for-buffer ()
  "Return a module name for the current buffer.
This is a name that the prover prefixes all item names with.
For example, in isabelle, a file Stuff.ML contains theorems with
fully qualified names of the form Stuff.theorem1, etc.
For other provers, this function may need modifying."
  (if buffer-file-name
      (file-name-nondirectory
       (file-name-sans-extension buffer-file-name)) ""))

(defun proof-depends-module-of (name)
  "Return a pair of a module name and base name for given item NAME.
Assumes module name is given by dotted prefix."
  (let ((dot (string-match "\\." name)))
    (if dot
	(cons (substring name 0 dot) (substring name (+ dot 1)))
      (cons "" name))))

(defun proof-depends-names-in-same-file (names)
  "Return subset of list NAMES which are guessed to occur in same file.
This is done using `proof-depends-module-name-for-buffer' and
`proof-depends-module-of'."
  (let ((filemod  (proof-depends-module-name-for-buffer))
	samefile)
    (while names
      (let ((splitname (proof-depends-module-of (car names))))
	(if (equal filemod (car splitname))
	    (setq samefile (cons (cdr splitname) samefile))))
      (setq names (cdr names)))
    ;; NB: reversed order
    samefile))


;;
;; proof-depends-process-dependencies: the main entry point.
;;
;;;###autoload
(defun proof-depends-process-dependencies (name gspan)
  "Process dependencies reported by prover, for NAME in span GSPAN.
Called from `proof-done-advancing' when a save is processed and
`proof-last-theorem-dependencies' is set."

  (span-set-property gspan 'dependencies
		     ;; Ancestors of NAME are in the second component.
		     ;; FIXME: for now we ignore the first component:
		     ;; NAME may not be enough [Isar allows proof regions
		     ;; with multiple names, which are reported in dep'c'y
		     ;; output].
		     (cdr proof-last-theorem-dependencies))

  (let* ((samefilenames    (proof-depends-names-in-same-file
			    (cdr proof-last-theorem-dependencies)))

	 ;; Find goalsave spans earlier in this file which this
	 ;; one depends on; update their list of dependents,
	 ;; and return resulting list paired up with names.
	 (depspans
	  (apply 'append
		 (span-mapcar-spans
		  (lambda (depspan)
		    (let ((dname (span-property depspan 'name)))
		      (if (and
			   (eq (span-property depspan 'type) 'goalsave)
			   (member dname samefilenames))
			  (let ((forwarddeps
				 (span-property depspan 'dependents)))
			    (span-set-property depspan 'dependents
					       (cons
						(list name gspan) forwarddeps))
			    ;; return list of args for menu fun: name and span
			    (list (list dname depspan))))))
		  (point-min)
		  (span-start gspan)
		  'type))))

    (span-set-property gspan 'dependencies-within-file depspans)
    (setq proof-last-theorem-dependencies nil)))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Menu Functions
;;
;; The following functions set up the menus which are the key way in
;; which the dependency information is used.


;;;###autoload
(defun proof-dependency-in-span-context-menu (span)
  "Make some menu entries showing proof dependencies of SPAN."
  ;; FIXME: might only activate this for dependency-relevant spans.
  (list
   "-------------"
   (proof-dep-make-submenu "Local Dependency..."
			   (lambda (namespan) (car namespan))
			   'proof-goto-dependency
			   (span-property span 'dependencies-within-file))
   (proof-make-highlight-depts-menu "Highlight Dependencies"
				    'proof-highlight-depcs
				    span 'dependencies-within-file)
   (proof-dep-make-submenu "Local Dependents..."
			   (lambda (namepos) (car namepos))
			   'proof-goto-dependency
			   (span-property span 'dependents))
   (proof-make-highlight-depts-menu "Highlight Dependents"
				    'proof-highlight-depts
				    span 'dependents)
   ["Unhighlight all" proof-dep-unhighlight t]
   "-------------"
   (proof-dep-alldeps-menu span)))

(defun proof-dep-alldeps-menu (span)
  (or (span-property span 'dependencies-menu) ;; cached value
      (span-set-property span 'dependencies-menu
			 (proof-dep-make-alldeps-menu
			  (span-property span 'dependencies)))))

(defun proof-dep-make-alldeps-menu (deps)
  (let ((menuname "All Dependencies...")
	(showdep  'proof-show-dependency))
    (if deps
	(let ((nestedtop   (proof-dep-split-deps deps)))
	  (cons menuname
		(append
		 (mapcar (lambda (l)
			   (vector l (list showdep l) t))
			 (cdr nestedtop))
		 (mapcar (lambda (sm)
			   (proof-dep-make-submenu (car sm)
						   'car
						   'proof-show-dependency
						   (mapcar 'list (cdr sm))))
			 (car nestedtop)))))
      (vector menuname nil nil))))

(defun proof-dep-split-deps (deps)
  "Split dependencies into named nested lists according to dotted prefixes."
  ;; NB: could handle deeper nesting here, but just do one level for now.
  (let (nested toplevel)
    ;; Add each name into a nested list or toplevel list
    (dolist (name deps)
      (let* ((period   (string-match "\\." name))
	     (ns       (and period (substring name 0 period)))
	     (subitems (and ns (assoc ns nested))))
	(cond
	 ((and ns subitems)
	  (setcdr subitems (adjoin name (cdr subitems))))
	 (ns
	  (setq nested
		(cons (cons ns (list name)) nested)))
	 (t
	  (setq toplevel (adjoin name  toplevel))))))
    (cons nested toplevel)))

(defun proof-dep-make-submenu (name namefn appfn list)
  "Make menu items for a submenu NAME, using APPFN applied to each elt in LIST.
If LIST is empty, return a disabled menu item with NAME.
NAMEFN is applied to each element of LIST to make the names."
  (if list
      (cons name
	    (mapcar `(lambda (l)
		       (vector (,namefn l)
			       (cons (quote ,appfn) l) t)) list))
    (vector name nil nil)))

(defun proof-make-highlight-depts-menu (name fn span prop)
  "Return a menu item that for highlighting dependents/depencies of SPAN."
  (let ((deps (span-property span prop)))
    (vector name `(,fn ,(span-property span 'name) (quote ,deps))
	    (not (not deps)))))


;;
;; Functions triggered by menus
;;

(defun proof-goto-dependency (name span)
  "Go to the start of SPAN."
  ;; FIXME: check buffer is right one.  Later we'll allow switching buffer
  ;; here and jumping to different files.
  (goto-char (span-start span))
  (skip-chars-forward " \t\n"))

(defun proof-show-dependency (thm)
  "Show dependency THM using `proof-show-dependency-cmd'.
This is simply to display the dependency somehow."
  (if proof-shell-show-dependency-cmd ;; robustness
      (proof-shell-invisible-command
       (format proof-shell-show-dependency-cmd thm))))

(defconst pg-dep-span-priority 500)
(defconst pg-ordinary-span-priority 100)

(defun proof-highlight-depcs (name nmspans)
  (let ((helpmsg  (concat "This item is a dependency (ancestor) of " name)))
    (while nmspans
      (let ((span (cadar nmspans)))
	(proof-depends-save-old-face span)
	(span-set-property span 'face 'proof-highlight-dependency-face)
	(span-set-property span 'priority pg-dep-span-priority)
	(span-set-property span 'mouse-highlight nil)
	(span-set-property span 'help-echo helpmsg))
      (setq nmspans (cdr nmspans)))))

(defun proof-highlight-depts (name nmspans)
  (let ((helpmsg  (concat "This item depends on (is a child of) " name)))
    (while nmspans
      (let ((span (cadar nmspans)))
	(proof-depends-save-old-face span)
	(span-set-property span 'face 'proof-highlight-dependent-face)
	(span-set-property span 'priority pg-dep-span-priority)
	(span-set-property span 'mouse-highlight nil)
	(span-set-property span 'help-echo helpmsg)
	(span-set-property span 'balloon-help helpmsg))
      (setq nmspans (cdr nmspans)))))

(defun proof-depends-save-old-face (span)
  (unless (span-property span 'depends-old-face)
    (span-set-property span 'depends-old-face
		       (span-property span 'face))))

(defun proof-depends-restore-old-face (span)
  (when (span-property span 'depends-old-face)
    (span-set-property span 'face
		       (span-property span 'depends-old-face))
    (span-set-property span 'depends-old-face nil)))

(defun proof-dep-unhighlight ()
  "Remove additional highlighting on all spans in file to their default."
  (interactive)
  (save-excursion
    (let ((span (span-at (point-min) 'type)))
      ;; FIXME: covers too many spans!
      (while span
	(pg-set-span-helphighlights span 'nohighlight)
	(proof-depends-restore-old-face span)
	(span-set-property span 'priority pg-ordinary-span-priority)
	(setq span (next-span span 'type))))))




(provide 'proof-depends)
;; proof-depends.el ends here

(provide 'proof-depends)

;;; proof-depends.el ends here
