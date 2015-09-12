;;; local-vars.el --- local variables list utilities
;;
;; Copyright (C) 2006 Pierre Courtieu
;; Authors: Pierre Courtieu
;; Maintainer: Pierre Courtieu <Pierre.Courtieu@cnam.fr>
;;
;; local-vars-list.el,v 12.1 2012/07/11 09:08:13 pier Exp

;; This software is free software; you can redistribute it and/or
;; modify it under the terms of the GNU General Public
;; License version 2, as published by the Free Software Foundation.
;;
;; This software is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
;;
;; See the GNU General Public License version 2 for more details
;; (enclosed in the file GPL).

;;; Commentary:
;; See documentation in variable local-var-list-doc

;;; History:
;;

;;; Help:

(defconst local-vars-list-doc nil
"From Emacs Info:

A file can contain a \"local variables list\", which specifies the values to use for
certain Emacs variables when that file is edited. See info node \"(emacs)File
Variables\".

local-vars-list provides two useful functions:

\\[local-vars-list-get] that reads a local variable value at the end of the file.

\\[local-vars-list-set] that writes a local variable value at the end of the file.")



(defun local-vars-list-find ()
  "Find the local variable definition paragraph.
Return a list containing the prefix and the suffix of its first line,
or throw 'notfound if not found. Sets the point at the beginning of
the second line of the paragraph."
  (goto-char (point-max))
  (catch 'notfound
    (if (not (re-search-backward "Local Variables:" nil t)) (throw 'notfound nil))
    (let ((bol (save-excursion (beginning-of-line) (point)))
	  (eol (save-excursion (end-of-line) (point)))
	  (lpattern)
	  (rpattern))
      (setq lpattern (buffer-substring bol (point)))
      (re-search-forward "Local Variables:" eol t)
      (setq rpattern (buffer-substring (point) eol))
      (forward-line 1)
      (beginning-of-line)
      (cons lpattern (cons rpattern nil)))))

(defun local-vars-list-goto-var (symb lpat rpat)
  "Search a line defining local variable symb at current line and below.
If successful set point to the beginning of the *value* and return t.
Otherwise set point to the beginning of the last line of the local
variables list (the one containing \"End:\"), and return nil.

lpat and rpat are the suffix and prefix of the local variable list.

Note: this function must be called when at the beginning of a local
variable definition (or at the \"End:\" line)."
  (let* ((symbname (symbol-name symb))
	 (found nil) (endreached nil)
	 (eol))
    (while (and (not found) (not endreached))
      (setq eol (save-excursion (end-of-line) (point)))
      (search-forward lpat eol)
      (re-search-forward "\\([^ :]+\\):" eol)
      (let ((varname (match-string 1)))
	(cond
	 ((string-equal varname "End") (setq endreached t) (beginning-of-line))
	 ((string-equal varname symbname) (setq found t))
	 (t (forward-line 1) (beginning-of-line)))))
    (if found t nil)))


; precond: really be on a var def line
(defun local-vars-list-get-current (lpat rpat)
  "Return the value written in the local variable list at current line.

lpat and rpat are the suffix and prefix of the local variable list.

Note: this function must be called when at the beginning of a local
variable definition (or at the \"End:\" line)."
  (let ((bol (save-excursion (beginning-of-line) (point)))
	(eol (save-excursion (end-of-line) (point)))
	(varname ""))
    (catch 'notfound
      (if (not (search-forward lpat eol t)) (throw 'notfound nil))
      (if (not (re-search-forward "\\([^ :]+\\):" eol t)) (throw 'notfound nil))
      (setq varname (match-string 1))
      (let ((boexp (point)))
	(if (not (search-forward rpat eol t)) (throw 'notfound nil))
	(search-backward rpat bol)	; should always succeed
	(read (buffer-substring boexp (point))))))) ; TODO: catch errors here?



(defun local-vars-list-get (symb)
  "Return the value written in the local variable list for variable symb.
Raises an error if symb is not in the list.

Note: Using `file-local-variables-alist' is not comfortable here
since editing by hand the file variable zone does not modify this
alist. Proceed by looking in the file instead."
  (save-excursion
    (let*
	((lrpat (local-vars-list-find))
	 (dummy (if lrpat t (error "local variables zone not found. ")))
	 (lpat (car lrpat))
	 (rpat (car (cdr lrpat)))
	 )
      (beginning-of-line)
      (if (local-vars-list-goto-var symb lpat rpat)
	  t
	(error "variable %s not found" symb))
      (beginning-of-line)
      (local-vars-list-get-current lpat rpat))))

(defun local-vars-list-get-safe (symb)
  "Return true if variable SYMB belongs to the local variable list of the
current buffer."
  (condition-case nil (local-vars-list-get symb) (error nil)))

(defun local-vars-list-set (symb val)
  "Write the value val in the local variable list for variable symb.
If the variable is already specified in the list, replace the
value. If no local variable list is found, create one at the end
of the buffer first."
  (add-file-local-variable symb val))


(provide 'local-vars-list)



;;; Local Variables: ***
;;; fill-column: 85 ***
;;; indent-tabs-mode: nil ***
;;; End: ***
