;; plastic-syntax.el - Syntax of Plastic
;; Author: Paul Callaghan <P.C.Callaghan@durham.ac.uk>
;; Maintainer: <author>
;; plastic-syntax.el,v 6.0 2001/09/03 12:11:56 da Exp

;; adapted from the following, by Paul Callaghan
;; ;; lego-syntax.el Syntax of LEGO
;; ;; Copyright (C) 1994 - 1998 LFCS Edinburgh.
;; ;; Author: Thomas Kleymann and Dilip Sequeira
;; ;; Maintainer: Paul Callaghan <P.C.Callaghan@durham.ac.uk>
;; ;; lego-syntax.el,v 2.10 1998/11/06 16:18:55 tms Exp


(require 'proof-syntax)

;; ----- keywords for font-lock.

(defconst plastic-keywords-goal '("$?Goal"))

(defconst plastic-keywords-save '("$?Save" "SaveFrozen" "SaveUnfrozen"))

(defconst plastic-commands
  (append plastic-keywords-goal plastic-keywords-save
	  '("allE" "allI" "andE" "andI" "Assumption" "Claim" "Coercion"
	    "Cut" "Discharge" "DischargeKeep"
	    "echo" "exE" "exI" "Expand" "ExpAll"
	    "ExportState" "Equiv" "For" "Freeze" "Hnf" "Immed"
	    "impE" "impI" "Induction" "Inductive"
	    "Invert" "Init" "intros" "Intros" "Module" "Next"
	    "Normal" "notE" "notI" "orE" "orIL" "orIR" "qnify" "Qnify"
	    "Qrepl" "Record" "Refine" "Repeat" "Return" "ReturnAll"
	    "Try" "Unfreeze"))
  "Subset of Plastic keywords and tacticals which are terminated by a \?;")

(defconst plastic-keywords
  (append plastic-commands
	  '("Constructors" "Double" "ElimOver" "Fields" "Import" "Inversion"
	    "NoReductions" "Parameters" "Relation" "Theorems")))

(defconst plastic-tacticals '("Then" "Else" "Try" "Repeat" "For"))

;; ----- regular expressions for font-lock
(defconst plastic-error-regexp "^\\(FAIL\\)"
  "A regular expression indicating that the Plastic process has identified an error.")

(defvar plastic-id proof-id)

(defvar plastic-ids (concat plastic-id "\\(\\s *,\\s *" plastic-id "\\)*")
  "*For font-lock, we treat \",\" separated identifiers as one identifier
  and refontify commata using \\{plastic-fixup-change}.")

(defconst plastic-arg-list-regexp "\\s *\\(\\[[^]]+\\]\\s *\\)*"
  "Regular expression maching a list of arguments.")

(defun plastic-decl-defn-regexp (char)
    (concat "\\[\\s *\\(" plastic-ids "\\)" plastic-arg-list-regexp char))
; Examples
;              ^        ^^^^        ^^^^^^^^^^^^^^^^^^^^^^^  ^^^^
;              [        sort                                 =
;              [        sort        [n:nat]                  =
;              [        sort        [abbrev=...][n:nat]      =

(defconst plastic-definiendum-alternative-regexp
  (concat "\\(" plastic-id "\\)" plastic-arg-list-regexp "\\s * ==")
  "Regular expression where the first match identifies the definiendum.")

(defvar plastic-font-lock-terms
  (list

   ; lambda binders
     (list (plastic-decl-defn-regexp "[:|?]") 1
	   'proof-declaration-name-face)

     ; let binders
     (list plastic-definiendum-alternative-regexp 1 'font-lock-function-name-face)
     (list (plastic-decl-defn-regexp "=") 1 'font-lock-function-name-face)

     ; Pi and Sigma binders
     (list (concat "[{<]\\s *\\(" plastic-ids "\\)") 1
	   'proof-declaration-name-face)

     ;; Kinds
     (cons (concat "\\<Prop\\>\\|\\<Type\\s *\\(("
		   plastic-id ")\\)?") 'font-lock-type-face))
  "*Font-lock table for Plastic terms.")

;; Instead of "[^:]+", it may be better to use "plastic-id". Furthermore,
;; it might be safer to append "\\s-*:".
(defconst plastic-goal-with-hole-regexp
  (concat "\\(" (proof-ids-to-regexp plastic-keywords-goal) "\\)\\s-+\\([^:]+\\)")
  "Regular expression which matches an entry in `plastic-keywords-goal'
  and the name of the goal.")

(defconst plastic-save-with-hole-regexp
  (concat "\\(" (proof-ids-to-regexp plastic-keywords-save) "\\)\\s-+\\([^;]+\\)")
  "Regular expression which matches an entry in
  `plastic-keywords-save' and the name of the goal.")

(defvar plastic-font-lock-keywords-1
   (append
    plastic-font-lock-terms
    (list
     (cons (proof-ids-to-regexp plastic-keywords) 'font-lock-keyword-face)
     (cons (proof-ids-to-regexp plastic-tacticals) 'proof-tacticals-name-face)
     (list plastic-goal-with-hole-regexp 2 'font-lock-function-name-face)
     (list plastic-save-with-hole-regexp 2 'font-lock-function-name-face))))

(defun plastic-init-syntax-table ()
  "Set appropriate values for syntax table in current buffer."

  (modify-syntax-entry ?_ "_")
  (modify-syntax-entry ?\' "_")
  (modify-syntax-entry ?\| ".")
  (modify-syntax-entry ?\* ". 23")
  (modify-syntax-entry ?\( "()1")
  (modify-syntax-entry ?\) ")(4"))


(provide 'plastic-syntax)
