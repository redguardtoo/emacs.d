;; hol98.el   Basic Proof General instance for HOL 98
;;
;; Copyright (C) 2000 LFCS Edinburgh.
;;
;; Author: David Aspinall <David.Aspinall@ed.ac.uk>
;;
;; hol98.el,v 12.0 2011/10/13 10:54:49 da Exp
;;
;; Needs improvement!
;;
;; See the README file in this directory for information.


(require 'proof-easy-config)            ; easy configure mechanism
(require 'proof-syntax)			; functions for making regexps

(defvar hol98-keywords nil)
(defvar hol98-rules nil)
(defvar hol98-tactics nil)
(defvar hol98-tacticals nil)

(proof-easy-config  'hol98 "HOL"
 proof-prog-name		 "hol.unquote"
 proof-terminal-string             ";"
 proof-script-comment-start             "(*"
 proof-script-comment-end               "*)"
 ;; These are all approximations, of course.
 proof-goal-command-regexp     "^g[ `]"
 proof-save-command-regexp     "pg_top_thm_and_drop"
 proof-goal-with-hole-regexp   "val \\(\\([^ \t=]*\\)\\)[ \t]*=[ \t]*prove"
 proof-save-with-hole-regexp   "val \\(\\([^ \t=]*\\)\\)[ \t]*=[ \t]*top_thm()"
 proof-non-undoables-regexp      "b()" ; and others..
 proof-goal-command              "g `%s`;"
 proof-save-command              "val %s = pg_top_thm_and_drop();"
 proof-kill-goal-command         "drop();"
 proof-showproof-command         "p()"
 proof-undo-n-times-cmd          "(pg_repeat backup %s; p());"
 proof-auto-multiple-files       t
 proof-shell-cd-cmd              "FileSys.chDir \"%s\""
 proof-shell-filename-escapes    '(("\\\\" . "\\\\") ("\""   . "\\\""))
 proof-shell-interrupt-regexp    "Interrupted"
 proof-shell-start-goals-regexp
 (proof-regexp-alt "Proof manager status"
		   "OK.."
		   "val it =\n")
 proof-shell-end-goals-regexp
 (proof-regexp-alt "^[ \t]*: GoalstackPure.goalstack"
		   "^[ \t]*: GoalstackPure.proofs")
 proof-shell-quit-cmd            "quit();"
 proof-assistant-home-page
 "http://www.cl.cam.ac.uk/Research/HVG/HOL/HOL.html"
 proof-shell-annotated-prompt-regexp
 "^- "
 ;; This one is nice but less reliable, I think.
 ;; "\\(> val it = () : unit\n\\)?- "
 proof-shell-error-regexp "^! "
 proof-shell-init-cmd
 "Help.displayLines:=3000;
  fun pg_repeat f 0 = () | pg_repeat f n = (f(); pg_repeat f (n-1));
  fun pg_top_thm_and_drop () = let val t = top_thm(); in (drop(); t) end;"
 ;; FIXME: add optional help topic parameter to help command.
 proof-info-command		    "help \"hol\""
 proof-shell-proof-completed-regexp "Initial goal proved"
 ;; FIXME: next one needs setting so that "urgent" messages are displayed
 ;; eagerly from HOL.
 ;; proof-shell-eager-annotation-start
 proof-find-theorems-command	"DB.match [] (%s);"

 proof-forget-id-command	";" ;; vacuous: but empty string doesn't give
				    ;; new prompt
 ;; We must force this to use ptys since mosml doesn't flush its output
 ;; (on Linux, presumably on Solaris too).
 proof-shell-process-connection-type t

 ;;
 ;; Syntax table entries for proof scripts
 ;;
 proof-script-syntax-table-entries
 '(?\` "\""
   ?\$ "."
   ?\/ "."
   ?\\ "."
   ?+  "."
   ?-  "."
   ?=  "."
   ?%  "."
   ?<  "."
   ?>  "."
   ?\& "."
   ?.  "w"
   ?_  "w"
   ?\' "w"
   ?\| "."
   ?\* ". 23"
   ?\( "()1"
   ?\) ")(4")

 ;;
 ;; A few of the vast variety of keywords, tactics, tacticals,
 ;; for decorating proof scripts.
 ;;
 ;; In the future, PG will use a mechanism for passing identifier
 ;; lists like this from the proof assistant, we don't really
 ;; want to duplicate the information here!
 ;;
 hol98-keywords  '("g" "expand" "e" "val" "store_thm" "top_thm" "by"
		   "pg_top_thm_and_drop"
		   "Define" "xDefine" "Hol_defn"
		   "Induct" "Cases" "Cases_on" "Induct_on"
		   "std_ss" "arith_ss" "list_ss"
		   "define_type")
 hol98-rules	 '("ASSUME" "REFL" "BETA_CONV" "SUBST"
		   "ABS" "INST_TYPE" "DISCH" "MP"
		   "T_DEF" "FORALL_DEF" "AND_DEF" "OR_DEF" "F_DEF"
		   "NOT_DEF" "EXISTS_UNIQUE_DEF" "BOOL_CASES_AX"
		   "IMP_ANTISYM_AX" "ETA_AX" "SELECT_AX" "ONE_ONE_DEF"
		   "ONTO_DEF" "INFINITY_AX" "LET_DEF" "COND_DEF" "ARB_DEF")
 hol98-tactics   '("ACCEPT_TAC" "ASSUME_TAC" "GEN_TAC"
		   "CONJ_TAC" "DISCH_TAC" "STRIP_TAC"
		   "SUBST_TAC" "ASM_CASES_TAC" "DISJ_CASES_TAC"
		   "REWRITE_TAC" "IMP_RES_TAC" "ALL_TAC" "NO_TAC"
		   "EQ_TAC" "EXISTS_TAC" "INDUCT_TAC"
		   "POP_ASM" "SUBST1_TAC" "ASSUM_LIST"
		   "PROVE" "PROVE_TAC" "DECIDE" "DECIDE_TAC" "RW_TAC"
		   "STP_TAC" "ZAP_TAC"
		   "EXISTS_TAC")
 hol98-tacticals '("ORELSE" "FIRST" "CHANGED_TAC" "THEN"
		   "THENL" "EVERY" "REPEAT"
		   "MAP_EVERY")
 proof-script-font-lock-keywords
 (list
  (cons (proof-ids-to-regexp hol98-keywords) 'font-lock-keyword-face)
  (cons (proof-ids-to-regexp hol98-tactics) 'font-lock-keyword-face)
  ; (cons (proof-ids-to-regexp hol98-rules) 'font-lock-keyword-face)
  (cons (proof-ids-to-regexp hol98-tacticals) 'proof-tacticals-name-face))

 ;;
 ;; Some decoration of the goals output
 ;;
 proof-goals-font-lock-keywords
 (list
  (cons (proof-ids-to-regexp '("Proof manager status"
			       "proof" "Incomplete"
			       "Initial goal proved"
			       "Initial goal"
			       "There are currently no proofs"
			       "OK"))
	'font-lock-keyword-face)
  (cons (regexp-quote "------------------------------------")
	'font-lock-comment-face)
  (cons ": GoalstackPure.goalstack" 'proof-boring-face)
  (cons ": GoalstackPure.proofs"    'proof-boring-face)
  (cons ": Thm.thm"		    'proof-boring-face)
  (cons "val it ="		    'proof-boring-face))

 ;; End of easy config.
 )


(warn "Hol Proof General is incomplete!  Please help improve it!
Read the manual, make improvements and send them to da+pg-feedback@inf.ed.ac.uk")

(provide 'hol98)
