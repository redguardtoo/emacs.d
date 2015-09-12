;; isar-find-theorems.el    A search form for Isabelle's find_theorems command.
;;
;; Copyright (C) 2007 Tjark Weber <tjark.weber@gmx.de>
;;
;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the GNU General Public License
;; as published by the Free Software Foundation; either version 2
;; of the License, or (at your option) any later version.
;;
;; isar-find-theorems.el,v 12.0 2011/10/13 10:54:50 da Exp
;;

(require 'pg-vars)
(declare-function proof-find-theorems "pg-user")


;; search form field values

(defvar isar-find-theorems-data (list
  ""      ;; num
  ""      ;; pattern
  "none"  ;; intro
  "none"  ;; elim
  "none"  ;; dest
  ""      ;; name
  ""      ;; simp
  )
  "Values of the Find Theorems search form's fields.")

;; make the original (minibuffer based) "Find theorems" command (from
;; ../generic/pg-user.el) available as isar-find-theorems-minibuffer;
;; return '(nil) so that isar-find-theorems-minibuffer works as a
;; value for isar-find-theorems-command

(defun isar-find-theorems-minibuffer ()
  "Search for items containing given constants (using the minibuffer)."
  (interactive)
  (let ((proof-find-theorems-command "find_theorems %s"))
    (call-interactively 'proof-find-theorems))
  '(nil))

;; isar-find-theorems-form (just like isar-find-theorems-minibuffer) can be
;; called interactively, and can be used as a value for
;; proof-find-theorems-command (returning '(nil) means that the actual
;; "find_theorems" command will NOT be issued to Isabelle by
;; proof-find-theorems in this case, but only later on by a handler function
;; for the form's "Find" button)

(defun isar-find-theorems-form ()
  "Search for items containing given constants (using a search form)."
  (interactive)
  (apply 'isar-find-theorems-create-searchform isar-find-theorems-data)
  '(nil))

;; update the universal key bindings (see ../generic/pg-vars.el)
;;
;; C-c C-a C-m is bound to isar-find-theorems-minibuffer
;; C-c C-a C-f is bound to isar-find-theorems-form
;;
;; Note that C-c C-a C-f, although C-c C-a usually invokes the prover
;; assistant specific keymap, is defined as a universal key binding here.
;; This way it will be available in the same buffers as C-c C-f.

(setq proof-universal-keys
  (cons
    '([(control c) (control a) (control m)] . isar-find-theorems-minibuffer)
    (cons
      '([(control c) (control a) (control f)] . isar-find-theorems-form)
      proof-universal-keys)))

;; Documentation, taken from isabelle/NEWS:
;;
;; * Command 'find_theorems' searches for a list of criteria instead of a
;; list of constants. Known criteria are: intro, elim, dest, name:string,
;; simp:term, and any term. Criteria can be preceded by '-' to select
;; theorems that do not match. Intro, elim, dest select theorems that
;; match the current goal, name:s selects theorems whose fully qualified
;; name contain s, and simp:term selects all simplification rules whose
;; lhs match term.  Any other term is interpreted as pattern and selects
;; all theorems matching the pattern. Available in ProofGeneral under
;; 'ProofGeneral -> Find Theorems' or C-c C-f.  Example:
;;
;;   C-c C-f (100) "(_::nat) + _ + _" intro -name: "HOL."
;;
;; prints the last 100 theorems matching the pattern "(_::nat) + _ + _",
;; matching the current goal as introduction rule and not having "HOL."
;; in their name (i.e. not being defined in theory HOL).

;; search form widgets (set in isar-find-theorems-create-searchform
;; and accessed in the "Find" handler)

(defvar isar-find-theorems-widget-number nil
  "Search form widget for the number of theorems.")

(defvar isar-find-theorems-widget-pattern nil
  "Search form widget for search patterns.")

(defvar isar-find-theorems-widget-intro nil
  "Search form widget for intro rules.")

(defvar isar-find-theorems-widget-elim nil
  "Search form widget for elim rules.")

(defvar isar-find-theorems-widget-dest nil
  "Search form widget for dest rules.")

(defvar isar-find-theorems-widget-name nil
  "Search form widget for theorem names.")

(defvar isar-find-theorems-widget-simp nil
  "Search form widget for simplification rules.")

;; creates (or switches to) the search form buffer

(defun isar-find-theorems-create-searchform
    (num pattern intro elim dest name simp &optional errmsg)
  "Create (or switch to) the Find Theorems search form buffer."

  (if (get-buffer "*Find Theorems*")
    (switch-to-buffer "*Find Theorems*")

  ;; create a new search form

  (switch-to-buffer "*Find Theorems*")

  (widget-insert
    (concat "\n  "
      (if (fboundp 'propertize)
	(propertize "Find Theorems" 'face 'bold)
      "Find Theorems")
      "\n\n"))

  ;; pattern
  (widget-insert "  Search pattern: ")
  (setq isar-find-theorems-widget-pattern (widget-create 'editable-field
    :size 50
    :help-echo "A pattern to match in the theorem."
    pattern))
  (widget-insert " ")
  (widget-create 'push-button
    :help-echo "Click <mouse-2> for help."
    :notify (lambda (&rest ignore) (isar-find-theorems-create-help))
    "?")

  ;; name
  (widget-insert "\n\n  Theorem name:   ")
  (setq isar-find-theorems-widget-name (widget-create 'editable-field
    :size 50
    :help-echo "Part of the theorem's name."
    name))
  (widget-insert " ")
  (widget-create 'push-button
    :help-echo "Click <mouse-2> for help."
    :notify (lambda (&rest ignore) (isar-find-theorems-create-help))
    "?")

  ;; intro
  (widget-insert "\n\n  Rules matching the current goal: ")
  (widget-create 'push-button
    :help-echo "Click <mouse-2> for help."
    :notify (lambda (&rest ignore) (isar-find-theorems-create-help))
    "?")
  (widget-insert "\n\n    INTRO:\n      ")
    (setq isar-find-theorems-widget-intro (widget-create 'radio-button-choice
    :value intro
    :indent 6
    :button-args (list :help-echo "Click <mouse-2> to select one option.")
    '(item "none") '(item "intro") '(item "-intro")))

  ;; elim
  (widget-insert "\n    ELIM:\n      ")
  (setq isar-find-theorems-widget-elim (widget-create 'radio-button-choice
    :value elim
    :indent 6
    :button-args (list :help-echo "Click <mouse-2> to select one option.")
    '(item "none") '(item "elim") '(item "-elim")))

  ;; dest
  (widget-insert "\n    DEST:\n      ")
  (setq isar-find-theorems-widget-dest (widget-create 'radio-button-choice
    :value dest
    :indent 6
    :button-args (list :help-echo "Click <mouse-2> to select one option.")
    '(item "none") '(item "dest") '(item "-dest")))

  ;; simp
  (widget-insert "\n  Simplification pattern: ")
  (setq isar-find-theorems-widget-simp (widget-create 'editable-field
    :size 42
    :help-echo
      "A pattern to match in the left-hand side of a simplification rule."
    simp))
  (widget-insert " ")
  (widget-create 'push-button
    :help-echo "Click <mouse-2> for help."
    :notify (lambda (&rest ignore) (isar-find-theorems-create-help))
    "?")

  ;; num
  (widget-insert "\n\n  Number of results:      ")
  (setq isar-find-theorems-widget-number (widget-create 'editable-field
    :size 10
    :help-echo "Maximum number of results to be displayed."
    num))
  (widget-insert " ")
  (widget-create 'push-button
    :help-echo "Click <mouse-2> for help."
    :notify (lambda (&rest ignore) (isar-find-theorems-create-help))
    "?")

  ;; Find
  (widget-insert "\n\n  ")
    (widget-create 'push-button
    :help-echo "Click <mouse-2> to submit this form."
    :notify (lambda (&rest ignore)
      (let ((num     (widget-value isar-find-theorems-widget-number))
	    (pattern (widget-value isar-find-theorems-widget-pattern))
	    (intro   (widget-value isar-find-theorems-widget-intro))
	    (elim    (widget-value isar-find-theorems-widget-elim))
	    (dest    (widget-value isar-find-theorems-widget-dest))
	    (name    (widget-value isar-find-theorems-widget-name))
	    (simp    (widget-value isar-find-theorems-widget-simp)))
      (kill-buffer "*Find Theorems*")
      (isar-find-theorems-submit-searchform
	num pattern intro elim dest name simp)))
    "Find")

  ;; Reset form
    (widget-insert "    ")
    (widget-create 'push-button
    :help-echo "Click <mouse-2> to reset this form."
    :notify (lambda (&rest ignore)
      (kill-buffer "*Find Theorems*")
      (isar-find-theorems-create-searchform
	"" "" "none" "none" "none" "" ""))
    "Reset Form")
    (widget-insert "\n")

  ;; errmsg
  (if errmsg
    (widget-insert (concat "\n    "
      (if (fboundp 'propertize)
	(propertize (concat errmsg "\n    See help for details.") 'face 'bold)
      (concat errmsg "\n    See help for details."))
      "\n")))

  (use-local-map widget-keymap)
  (widget-setup)

  (goto-char 37))  ;; beginning of the "Search pattern" text field
)

;; creates the search form help buffer

(defun isar-find-theorems-create-help ()
  "Create a help text buffer for the Find Theorems search form."

  (with-output-to-temp-buffer "*Find Theorems - Help*"
    (princ (concat
      "\n"
      "*** Find Theorems - Help ***\n"
      "\n"
      "Command \"Find Theorems\" (C-c C-f) searches for theorems that satisfy a list of\n"
      "user-supplied criteria. Known criteria are:\n"
      "\n"
      "* Search pattern: a pattern that occurs in the theorem, e.g. \"(_::nat) + _\".\n"
      "\n"
      "* Theorem name: a substring of the theorem's fully qualified name. (Treats \"*\"\n"
      "                as a wildcard character.)\n"
      "\n"
      "* Intro, Elim, Dest: select theorems that match the current goal as\n"
      "                     introduction/elimination/destruction rule.\n"
      "\n"
      "* Simplification pattern: selects simplification rules whose left-hand side\n"
      "                          matches the given pattern.\n"
      "\n"
      "* Number of results: an upper bound on the number of theorems that are\n"
      "                     displayed. (Leave empty to use Isabelle's default value.)\n"
      "\n"
      "Multiple search patterns, theorem names and simplification patterns can be\n"
      "given, separated by spaces. (Patterns containing a space must be enclosed in\n"
      "double-quotes.) Criteria can be preceded by \"-\" to select theorems that do not.\n"
      "match. (Patterns that begin with a \"-\" must be enclosed in double-quotes.)\n"
      "\n"
      "A minibuffer based \"Find Theorems\" command is available via (C-c C-a C-m). See\n"
      "the Isabelle NEWS file for up-to-date documentation. A search form is available\n"
      "via (C-c C-a C-f). Variable proof-find-theorems-command (customizable via\n"
      "Proof-General > Advanced > Internals > Prover Config) controls the default\n"
      "behavior of the \"Find Theorems\" command: set to isar-find-theorems-form or\n"
      "isar-find-theorems-minibuffer.\n"
  )))
)

;; parses the search form's data and calls isar-find-theorems
;; with an appropriate argument string, or displays the search
;; form again, but with an error message

(defun isar-find-theorems-submit-searchform
    (num pattern intro elim dest name simp)
  "Parse the Find Theorems search form's data."

  (let (num_ pattern_ intro_ elim_ dest_ name_ simp_ searchstring)

  ;; pattern
  (setq pattern_ (isar-find-theorems-parse-criteria "" pattern))

  (if (not (pop pattern_))
    (isar-find-theorems-create-searchform
      num pattern intro elim dest name simp
      (concat "Invalid search pattern: " (car pattern_)))

  (setq pattern_ (car pattern_))

  ;; name
  (setq name_ (isar-find-theorems-parse-criteria "name: " name))

  (if (not (pop name_))
    (isar-find-theorems-create-searchform
      num pattern intro elim dest name simp
      (concat "Invalid theorem name: " (car name_)))

  (setq name_ (car name_))

  ;; simp
  (setq simp_ (isar-find-theorems-parse-criteria "simp: " simp))

  (if (not (pop simp_))
    (isar-find-theorems-create-searchform
      num pattern intro elim dest name simp
      (concat "Invalid simplification pattern: " (car simp_)))

  (setq simp_ (car simp_))

  ;; num
  (setq num_ (isar-find-theorems-parse-number num))

  (if (not num_)
    (isar-find-theorems-create-searchform
      num pattern intro elim dest name simp
      "Number of results must be a positive integer.")

  ;; intro
  (setq intro_ (if (equal intro "none") "" intro))

  ;; elim
  (setq elim_ (if (equal elim "none") "" elim))

  ;; dest
  (setq dest_ (if (equal dest "none") "" dest))

  ;; success: save data, call isar-find-theorems
  (setq isar-find-theorems-data
    (list num pattern intro elim dest name simp))

  (setq searchstring (format "find_theorems %s"
    (mapconcat 'identity
      (isar-find-theorems-filter-empty
	(list num_ pattern_ intro_ elim_ dest_ name_ simp_))
      " ")))

  ;; note that proof-find-theorems with an argument provided
  ;; will merely pass this on to Isabelle, and NOT display
  ;; the search form again
  (proof-find-theorems searchstring))))))
)

;; "Multiple search patterns, theorem names and simplification terms can be
;; given, separated by spaces. (Patterns containing a space must be enclosed
;; in double-quotes.) Criteria can be preceded by "-" to select theorems that
;; do not match. (Patterns that begin with a "-" must be enclosed in double-
;; quotes.)"
;;
;; returns (t parsed-string) (where parsed-string may be empty) or
;; (nil errmsg) in case of an error

(defun isar-find-theorems-parse-criteria (option-string criteria-string)
  "Parse search patterns/theorem names/simplification terms,
separated by \" \", possibly preceded by \"-\", and possibly
escaped by double-quotes."

  ;; This code might benefit greatly from the use of regexps.

  (let ((tokens nil) (errmsg nil))

  ;; turn criteria-string into a list of (string) tokens
  (while (and (not (equal criteria-string "")) (not errmsg))

    ;; ignore space
    (if (equal (elt criteria-string 0) ?\ )
      (setq criteria-string (substring criteria-string 1))

    ;; - is a token
    ;; Note: This is still a bit weird, as it treats a - following a -
    ;;       just like the first -, i.e. not as part of a pattern. Oh
    ;;       well.
    (if (equal (elt criteria-string 0) ?-)
      (progn
	(setq tokens (cons "-" tokens))
	(setq criteria-string (substring criteria-string 1)))

    ;; " starts a token: search for the next ", regard as one token
    ;; Note: This is still a bit weird, as it does not require the
    ;;       closing double-quotes to be followed by a space. Oh well.
    (if (equal (elt criteria-string 0) ?\")
      (let ((i 1))
	(while (and (< i (length criteria-string))
		    (not (equal (elt criteria-string i) ?\")))
	  (setq i (1+ i)))
	(if (equal i (length criteria-string))
	  (setq errmsg "missing closing double-quotes.")
	(setq i (1+ i))
	(setq tokens (cons (substring criteria-string 0 i) tokens))
	(setq criteria-string (substring criteria-string i))))

    ;; everything else: search for the next space, regard as one token
    ;; Note: This is still a bit weird, as it scans over double-quotes.
    ;;       Oh well.
    (let ((i 1))
      (while (and (< i (length criteria-string))
		  (not (equal (elt criteria-string i) ?\ )))
	(setq i (1+ i)))
      (setq tokens (cons (substring criteria-string 0 i) tokens))
      (setq criteria-string (substring criteria-string i)))
    )))
  )

  (if errmsg
    (list nil errmsg)

  (setq tokens (nreverse tokens))

  ;; convert the tokens into argument strings; make sure every "-" is
  ;; followed by a pattern/name (i.e. not by another "-")
  (let ((strings nil) (negated nil))

  (while (and tokens (not errmsg))
    (let ((token (car tokens)))
    (if (equal token "-")
      (if negated
	(setq errmsg "- may not be followed by another -.")
      (setq negated t)
      (setq tokens (cdr tokens)))
    (setq strings (cons
      (concat (if negated "-" "") option-string
	;; wrap token in double-quotes if necessary
	(if (equal (elt token 0) ?\") token (concat "\"" token "\"")))
      strings))
    (setq negated nil)
    (setq tokens (cdr tokens))))
  )

  (if errmsg
    (list nil errmsg)

  (if negated
    (list nil "- must be followed by a search criterion.")

  (setq strings (nreverse strings))

  (list t (mapconcat 'identity strings " "))
  )))))
)

;; auxiliary functions

;; returns "" if num is "", "(num)" if num is a string encoding a positive
;; integer, and nil otherwise

(defun isar-find-theorems-parse-number (num)
  "Parse the number of theorems to be displayed."
  (if (equal num "")
    ""
  (let ((numval (string-to-number num)))
  (if (and (wholenump numval) (not (equal numval 0)))
    (concat "(" (number-to-string numval) ")")
  nil)))
)

(defun isar-find-theorems-filter-empty (strings)
  "Build a new list by removing empty strings from a (non-circular) list."
  (if (not strings)
    nil
  (if (equal (car strings) "")
    (isar-find-theorems-filter-empty (cdr strings))
  (cons (car strings)
    (isar-find-theorems-filter-empty (cdr strings)))))
)

(provide 'isar-find-theorems)
