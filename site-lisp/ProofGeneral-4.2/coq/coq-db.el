;;; coq-db.el --- coq keywords database utility functions
;;
;; Author: Pierre Courtieu <courtieu@lri.fr>
;; License:     GPL (GNU GENERAL PUBLIC LICENSE)
;;
;;
;;; Commentary:
;;
;; We store all information on keywords (tactics or command) in big
;; tables (ex: `coq-tactics-db') From there we get: menus including
;; "smart" commands, completions for command coq-insert-...
;; abbrev tables and font-lock keyword.
;;

;;; Code:

(eval-when-compile
  (require 'cl))

(require 'proof-config)			; for proof-face-specs, a macro
(require 'proof-syntax)			; for proof-ids-to-regexp
(require 'holes)

(defconst coq-syntax-db nil
  "Documentation-only variable, for coq keyword databases.
Each element of a keyword database contains the definition of a \"form\", of the
form:

\(MENUNAME ABBREV INSERT STATECH KWREG INSERT-FUN HIDE)

MENUNAME is the name of form (or form variant) as it should appear in menus or
completion lists.

ABBREV is the abbreviation for completion via \\[expand-abbrev].

INSERT is the complete text of the form, which may contain holes denoted by
\"#\" or \"@{xxx}\".

If non-nil the optional STATECH specifies that the command is not state
preserving for coq.

If non-nil the optional KWREG is the regexp to colorize correponding to the
keyword.  ex: \"simple\\\\s-+destruct\" (\\\\s-+ meaning \"one or more spaces\").
*WARNING*: A regexp longer than another one should be put FIRST. For example:

  (\"Module Type\" ... ... t \"Module\\s-+Type\")
  (\"Module\" ... ... t \"Module\")

Is ok because the longer regexp is recognized first.

If non-nil the optional INSERT-FUN is the function to be called when inserting
the form (instead of inserting INSERT, except when using \\[expand-abbrev]). This
allows to write functions asking for more information to assist the user.

If non-nil the optional HIDE specifies that this form should not appear in the
menu but only in interactive completions.

Example of what could be in your emacs init file:

\(defvar coq-user-tactics-db
  '(
    (\"mytac\" \"mt\" \"mytac # #\" t \"mytac\")
    (\"myassert by\" \"massb\" \"myassert ( # : # ) by #\" t \"assert\")
    ))

Explanation of the first line: the tactic menu entry mytac, abbreviated by mt,
will insert \"mytac # #\" where #s are holes to fill, and \"mytac\" becomes a
new keyword to colorize.")

(defun coq-insert-from-db (db prompt)
  "Ask for a keyword, with completion on keyword database DB and insert.
Insert corresponding string with holes at point.  If an insertion function is
present for the keyword, call it instead.  see `coq-syntax-db' for DB
structure."
  (let* ((tac (completing-read (concat prompt " (TAB for completion): ")
			       db nil nil))
	 (infos (cddr (assoc tac db)))
	 (s (car infos)) ; completion to insert
	 (f (car-safe (cdr-safe (cdr-safe (cdr infos))))) ; insertion function
	 (pt (point)))
    (if f (funcall f) ; call f if present
      (insert (or s tac)) ; insert completion and indent otherwise
      (holes-replace-string-by-holes-backward-jump pt)
      (indent-according-to-mode))))



(defun coq-build-regexp-list-from-db (db &optional filter)
  "Take a keyword database DB and return the list of regexps for font-lock.
If non-nil Optional argument FILTER is a function applying to each line of DB.
For each line if FILTER returns nil, then the keyword is not added to the
regexp.  See `coq-syntax-db' for DB structure."
  (let ((l db) res)
    (while l
      (let* ((hd (car l)) (tl (cdr l))	; hd is the first infos list
	     (color (nth 4 hd)))	; colorization string
; da: do this below, otherwise we get empty words in result!!
;	     (color (concat "\\_<" (nth 4 hd) "\\_>")))       ; colorization string
	;; TODO delete doublons
	(when (and color (or (not filter) (funcall filter hd)))
	  (setq res 
		(nconc res (list
			    (concat "\\_<" color "\\_>")))))
	(setq l tl)))
    res))

(defun coq-build-opt-regexp-from-db (db &optional filter)
  "Take a keyword database DB and return a regexps for font-lock.
If non-nil optional argument FILTER is a function applying to each line of DB.
For each line if FILTER returns nil, then the keyword is not added to the
regexp.  See `coq-syntax-db' for DB structure."
  (let ((l db) res)
    (while l
      (let* ((hd (car l)) (tl (cdr l))	; hd is the first infos list
	     (color (nth 4 hd)))       ; colorization string
	;; TODO delete doublons
	(when (and color (or (not filter) (funcall filter hd)))
	  (setq res (nconc res (list color)))) ; careful: nconc destructive!
	(setq l tl)))
; da: next call is wrong?
;    (proof-ids-to-regexp res)))
    (concat "\\_<\\(?:" (proof-regexp-alt-list res) "\\)\\_>")))


;; Computes the max length of strings in a list
(defun max-length-db (db)
  "Return the length of the longest first element (menu label) of DB.
See `coq-syntax-db' for DB structure."
  (let ((l db) (res 0))
    (while l
      (let ((lgth (length (car (car l)))))
	(setq res (max lgth res))
	(setq l (cdr l))))
    res))



(defun coq-build-menu-from-db-internal (db lgth menuwidth)
  "Take a keyword database DB and return one insertion submenu.
Argument LGTH is the max size of the submenu.  Argument MENUWIDTH is the width
of the largest line in the menu (without abbrev and shortcut specifications).
Used by `coq-build-menu-from-db', which you should probably use instead.  See
`coq-syntax-db' for DB structure."
  (let ((l db) (res ()) (size lgth)
	(keybind-abbrev (substitute-command-keys " \\[expand-abbrev]")))
    (while (and l (> size 0))
      (let* ((hd (car l))
	     (menu     	 (nth 0 hd)) ; e1 = menu entry
	     (abbrev   	 (nth 1 hd)) ; e2 = abbreviation
	     (complt   	 (nth 2 hd)) ; e3 = completion
	     (state    	 (nth 3 hd)) ; e4 = state changing
	     (color    	 (nth 4 hd)) ; e5 = colorization string
	     (insertfn 	 (nth 5 hd)) ; e6 = function for smart insertion
	     (menuhide 	 (nth 6 hd)) ; e7 = if non-nil : hide in menu
	     (entry-with (max (- menuwidth (length menu)) 0))
	     (spaces (make-string entry-with ? ))
	     ;;(restofmenu (coq-build-menu-from-db-internal tl (- size 1) menuwidth))
	     )
	(unless menuhide
	  (let ((menu-entry
		 (vector
		  ;; menu entry label
		  (concat menu 
			  (if (not abbrev) "" 
			    (concat spaces "(" abbrev keybind-abbrev ")")))
		  ;;insertion function if present otherwise insert completion
		  (if insertfn insertfn `(holes-insert-and-expand ,complt))
		  t)))
	    (setq res (nconc res (list menu-entry)))));; append *in place*
	(setq l (cdr l))
	(decf size)))
    res))


(defun coq-build-title-menu (db size)
  "Build a title for the first submenu of DB, of size SIZE.
Return the string made of the first and the SIZE nth first element of DB,
separated by \"...\".  Used by `coq-build-menu-from-db'.  See `coq-syntax-db'
for DB structure."
    (concat (car-safe (car-safe db))
	  " ... "
	  (car-safe (car-safe (nthcdr (- size 1) db)))))

(defun coq-sort-menu-entries (menu)
  (sort menu
	#'(lambda (x y) (string<
			 (downcase (elt x 0))
			 (downcase (elt y 0))))))

(defun coq-build-menu-from-db (db &optional size)
  "Take a keyword database DB and return a list of insertion menus for them.
Submenus contain SIZE entries (default 30).  See `coq-syntax-db' for DB
structure."
  ;; sort is destructive for the list, so copy list before sorting
  (let* ((l (coq-sort-menu-entries (copy-sequence db))) (res ())
	 (wdth (+ 2 (max-length-db db)))
	 (sz (or size 30)) (lgth (length l)))
    (while l
      (if (<= lgth sz)
	  (setq res ;; careful: nconc destructive!
		(nconc res (list (cons
				  (coq-build-title-menu l lgth)
				  (coq-build-menu-from-db-internal l lgth wdth)))))
	(setq res ; careful: nconc destructive!
	      (nconc res (list (cons
				(coq-build-title-menu l sz)
				(coq-build-menu-from-db-internal l sz wdth))))))
      (setq l (nthcdr sz l))
      (setq lgth (length l)))
    res))

(defcustom coq-holes-minor-mode t
  "*Whether to apply holes minor mode (see `holes-show-doc') in
  coq mode."
  :type 'boolean
  :group 'coq)

(defun coq-build-abbrev-table-from-db (db)
  "Take a keyword database DB and return an abbrev table.
See `coq-syntax-db' for DB structure."
  (let ((l db) (res ()))
    (while l
      (let* ((hd (car l))(tl (cdr l))	; hd is a list of length 3 or 4
	     (e1 (car hd)) (tl1 (cdr hd)) ; e1 = menu entry
	     (e2 (car tl1)) (tl2 (cdr tl1)) ; e2 = abbreviation
	     (e3 (car tl2)) (tl3 (cdr tl2)) ; e3 = completion
	     )
	;; careful: nconc destructive!
	(when e2
	  (push `(,e2 ,e3 ,(if coq-holes-minor-mode #'holes-abbrev-complete)
                      :system t)
                res))
	(setq l tl)))
    (nreverse res)))


(defun filter-state-preserving (l)
  ; checkdoc-params: (l)
  "Not documented."
  (not (nth 3 l))) ; fourth argument is nil --> state preserving command

(defun filter-state-changing (l)
  ; checkdoc-params: (l)
  "Not documented."
  (nth 3 l)) ; fourth argument is nil --> state preserving command


;;A new face for tactics which fail when they don't kill the current goal
(defface coq-solve-tactics-face
  (proof-face-specs
   (:foreground "red") ; pour les fonds clairs
   (:foreground "red") ; pour les fond foncés
   ()) ; pour le noir et blanc
  "Face for names of closing tactics in proof scripts."
  :group 'proof-faces)

;;A new face for cheating tactics 
(defface coq-cheat-face
  (proof-face-specs
   (:background "red") ; pour les fonds clairs
   (:background "red") ; pour les fond foncés
   ()) ; pour le noir et blanc
  "Face for names of cheating tactics in proof scripts."
  :group 'proof-faces)

(defconst coq-solve-tactics-face 'coq-solve-tactics-face
  "Expression that evaluates to a face.
Required so that 'proof-solve-tactics-face is a proper facename")

(defconst coq-cheat-face 'coq-cheat-face
  "Expression that evaluates to a face.
Required so that 'proof-solve-tactics-face is a proper facename")



(provide 'coq-db)

;;; coq-db.el ends here

;** Local Variables: ***
;** fill-column: 80 ***
;** End: ***
