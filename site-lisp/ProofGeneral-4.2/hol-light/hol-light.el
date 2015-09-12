;; hol-light.el   Basic Proof General instance for HOL Light
;;
;; Copyright (C) 2010-12 LFCS Edinburgh, David Aspinall.
;;
;; Author: David Aspinall <David.Aspinall@ed.ac.uk>
;;         Mark Adams <mark@proof-technologies.com>
;;
;; hol-light.el,v 12.19 2012/02/08 18:46:56 da Exp
;;
;; See the README file in this directory for information.
;;

(require 'proof-easy-config)            ; easy configure mechanism
(require 'proof-syntax)			; functions for making regexps

(or (proof-try-require 'caml-font)	  ; use OCaml Emacs mode syntax 
    (defvar caml-font-lock-keywords nil)) ;

(eval-when (compile)
 (require 'proof-tree)
 (defvar caml-font-lock-keywords nil))

(defcustom hol-light-home 
  (or (getenv "HOLLIGHT_HOME")
      (concat (getenv "HOME") "/hol_light"))
  "*Directory holding the local installation of HOL Light."
  :type 'string
  :group 'hol-light)

(defcustom hol-light-prog-name 
  (or (getenv "HOLLIGHT_OCMAL")
      (getenv "OCAML")
      "ocaml")
  "*Name of the OCaml interpreter to launch HOL Light."
  :type 'string
  :group 'hol-light)

(defcustom hol-light-use-custom-toplevel t
  "*If non-nil, we use a custom toplevel for Proof General.
This configures extra annotations inside HOL Light to help
recognise portions of output from the proof assistant.

If this is incompatible with your usage of HOL Light for
some reason, you can change this setting to run in a
degraded (less robust) way which interfaces with the
standard top level.

You need to restart Emacs if you change this setting."
  :type 'boolean
  :group 'hol-light)

(defconst hol-light-pre-sync-cmd
  (format "#use \"%shol-light/pg_prompt.ml\";; " proof-home-directory)
  "Command used to configure prompt annotations for Proof General.")

(defcustom hol-light-init-cmd 
  (append
   (list (format "#cd \"%s\"" hol-light-home)
	 "#use \"hol.ml\"")
   (if hol-light-use-custom-toplevel
       (list (format "#use \"%shol-light/pg_tactics.ml\""
		     proof-home-directory))
     (list
  "let rec pg_repeat f n = match n with 0 -> () | _ -> (f(); pg_repeat f (n-1));;"
  "let pg_undo n = (pg_repeat n (fun ()->let _ = b() in ()); p());;"
  "let pg_kill() = current_goalstack:=[];;"
  "let pg_forget id = ();;"
  "let pg_restart() = print_string \"*** Session restarted.\";;")))
  "*Commands used to start up a running HOL Light session."
  :type '(list string)
  :group 'hol-light)

;;
;; Regular expressions for matching output with  
;; standard or custom top levels
;;

(defconst hol-light-plain-start-goals-regexp
  (concat
  "^\\(val it : x?goalstack = \\)"
  "\\(?:.+\n\\)*"
  "\\(?:[0-9]*[0-9] subgoals? ([0-9]+ total)\\|No subgoals\\)")
  "Value for `proof-shell-start-goals-regexp' with standard top level.")

(defconst hol-light-annotated-start-goals-regexp 
  hol-light-plain-start-goals-regexp
  "Value for `proof-shell-start-goals-regexp' with custom top level.")

(defconst hol-light-plain-interrupt-regexp
  "Interrupted"
  "Value for `proof-shell-interrupt-regexp' with standard top level.")

(defconst hol-light-annotated-interrupt-regexp
  hol-light-plain-interrupt-regexp ;; TODO
  "Value for `proof-shell-interrupt-regexp' with custom top level.")  

(defconst hol-light-plain-prompt-regexp
  "\\(val it : unit = ()\n\\)?^# "
  "Value for `proof-shell-annotated-prompt-regexp' with standard top level.")

(defconst hol-light-annotated-prompt-regexp
  "\\(val it : unit = ()\n\\)?<prompt>.*</prompt>"
  "Value for `proof-shell-annotated-prompt-regexp' with custom top level.")

(defconst hol-light-plain-error-regexp
  (proof-regexp-alt "Characters [0-9]+-[0-9]+:" 
		    "^Exception: Failure"
		    "^Parse error: "
		    "^Cannot find file"
		    "^Error: Unbound value"
		    "^Error: Syntax error"
		    ;; TODO: more here
		    )
  "Value for `proof-shell-error-regexp' with standard top level.")

(defconst hol-light-annotated-error-regexp 
  ;; "<error>.+</error>" ;; unfortunately not enough, this is only for failwith
  hol-light-plain-error-regexp
  "Value for `proof-shell-error-regexp' with custom top level.")

(defconst hol-light-plain-proof-completed-regexp
   "Initial goal proved"
   "Value for `proof-shell-proof-completed-regexp' with standard top level.")

(defconst hol-light-annotated-proof-completed-regexp
  hol-light-plain-proof-completed-regexp ;; TODO
   "Value for `proof-shell-proof-completed-regexp' with standard top level.")

(defconst hol-light-plain-message-start 
  "^Warning \\|\\*\*\\*"
  "Value for `proof-shell-eager-annotation-start' with standard top level.")

(defconst hol-light-annotated-message-start
  "^Warning \\|\\*\\*\\*" ;; TODO
  "Value for `proof-shell-eager-annotation-start' with custom top level.")

(defconst hol-light-plain-message-end
  "\n" ;; TODO
  "Value for `proof-shell-eager-annotation-start' with standard top level.")

(defconst hol-light-annotated-message-end
  "\n" ;; TODO
  "Value for `proof-shell-eager-annotation-start' with custom top level.")
  

;;;
;;; State 
;;;

(defvar hol-light-keywords nil)
(defvar hol-light-rules nil)
(defvar hol-light-tactics nil)
(defvar hol-light-tacticals nil)


;;;
;;; Main configuration
;;;

(proof-easy-config  'hol-light "HOL Light"
 proof-assistant-home-page       "https://www.cl.cam.ac.uk/~jrh13/hol-light/"
 proof-prog-name		 hol-light-prog-name
 proof-terminal-string           ";;"
 proof-shell-pre-sync-init-cmd   hol-light-pre-sync-cmd
 proof-shell-init-cmd            hol-light-init-cmd

 ;; Regexps for matching tactic script inputs: all approximations, of course.
 proof-goal-command-regexp     	"^g[ `]"
 proof-save-command-regexp     	"top_thm()"
 proof-goal-with-hole-regexp   	"let \\(\\([^ \t=]*\\)\\)[ \t]*=[ \t]*prove"
 proof-save-with-hole-regexp   	"let \\(\\([^ \t=]*\\)\\)[ \t]*=[ \t]*top_thm()"
 proof-non-undoables-regexp    	"b()" ; and others..
 proof-goal-command            	"g `%s`;;"
 proof-save-command            	"val %s = top_thm();;"
 proof-kill-goal-command       	"pg_kill();;"
 proof-undo-n-times-cmd        	"pg_undo %s;;"
 proof-forget-id-command	"pg_forget \"%s\";;"
 proof-shell-restart-cmd        "pg_restart();;"
 proof-showproof-command       	"p();;"
 proof-auto-multiple-files     	t
 proof-shell-cd-cmd            	"#cd \"%s\";;"
 proof-shell-filename-escapes  	'(("\\\\" . "\\\\") ("\""   . "\\\""))

 proof-shell-annotated-prompt-regexp (if hol-light-use-custom-toplevel
					 hol-light-annotated-prompt-regexp
				       hol-light-plain-prompt-regexp)

 proof-shell-interrupt-regexp        (if hol-light-use-custom-toplevel
					 hol-light-annotated-interrupt-regexp
				       hol-light-plain-interrupt-regexp)

 proof-shell-start-goals-regexp      (if hol-light-use-custom-toplevel
					 hol-light-annotated-start-goals-regexp
				       hol-light-plain-start-goals-regexp)

 proof-shell-error-regexp	     (if hol-light-use-custom-toplevel
					 hol-light-annotated-error-regexp
				       hol-light-plain-error-regexp)

 proof-shell-proof-completed-regexp  (if hol-light-use-custom-toplevel
					 hol-light-annotated-proof-completed-regexp
				       hol-light-plain-proof-completed-regexp)

 proof-shell-eager-annotation-start  (if hol-light-use-custom-toplevel
					 hol-light-annotated-message-start
				       hol-light-plain-message-start)

 proof-shell-eager-annotation-end    (if hol-light-use-custom-toplevel
					 hol-light-annotated-message-end
				       hol-light-plain-message-end)

 
 ;; FIXME: add optional help topic parameter to help command.
 proof-info-command		    "help \"hol\""

 ;; FIXME: next one needs setting so that "urgent" messages are displayed
 ;; eagerly from HOL.
 ;; proof-shell-eager-annotation-start
 proof-find-theorems-command	"DB.match [] (%s);;"

 ;;
 ;; Syntax and syntax table entries for proof scripts
 ;;
 proof-script-comment-start      "(*"
 proof-script-comment-end        "*)"
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
   ?\* ". 23n"
   ?\( "()1"
   ?\) ")(4")

 ;;
 ;; A few of the vast variety of keywords, tactics, tacticals,
 ;; for decorating proof scripts.
 ;;
 ;; In the future, PG will use a mechanism for passing identifier
 ;; lists like this from the proof assistant, we don't really
 ;; want to duplicate all this information here!
 ;;
 hol-light-keywords  '("g" "expand" "e" "store_thm" "top_thm" "by"
		       "Define" "xDefine" "Hol_defn"
		       "Induct" "Cases" "Cases_on" "Induct_on"
		       "std_ss" "arith_ss" "list_ss"
		       "define_type")

 hol-light-rules	 
 '("REFL" "TRANS" "MK_COMB" "ABS" "BETA" "BETA_CONV"
   "ASSUME" "EQ_MP" "DEDUCT_ANTISYM_RULE" "INST_TYPE" "INST"
   "TRUTH" "CONJ" "CONJUNCT1" "CONJUNCT2" "PINST" "PROVE_HYP"
   "T_DEF" "TRUTH" "EQT_ELIM" "EQT_INTRO" "AND_DEF" "CONJ"
   "CONJUNCT1" "CONJUNCT2" "CONJ_PAIR" "CONJUNCTS" "IMP_DEF" "MP"
   "DISCH" "DISCH_ALL" "UNDISCH" "UNDISCH_ALL" "IMP_ANTISYM_RULE" "ADD_ASSUM"
   "EQ_IMP_RULE" "IMP_TRANS" "FORALL_DEF" "SPEC" "SPECL" "SPEC_VAR"
   "SPEC_ALL" "ISPEC" "ISPECL" "GEN" "GENL" "GEN_ALL th"
   "EXISTS_DEF" "EXISTS" "SIMPLE_EXISTS" "CHOOSE" "SIMPLE_CHOOSE" "OR_DEF"
   "DISJ1" "DISJ2" "DISJ_CASES" "SIMPLE_DISJ_CASES" "F_DEF" "NOT_DEF"
   "NOT_ELIM" "NOT_INTRO" "EQF_INTRO" "EQF_ELIM" "CONTR" "EXISTS_UNIQUE_DEF"
   "EXISTENCE"
   "EQ_REFL" "REFL_CLAUSE" "EQ_SYM" "EQ_SYM_EQ" "EQ_TRANS"
   "AC" "BETA_THM" "ABS_SIMP" "CONJ_ASSOC" "CONJ_SYM"
   "CONJ_ACI" "DISJ_ASSOC" "DISJ_SYM" "DISJ_ACI" "IMP_CONJ"
   "IMP_IMP" "IMP_CONJ_ALT" "LEFT_OR_DISTRIB" "RIGHT_OR_DISTRIB" "FORALL_SIMP"
   "EXISTS_SIMP" "EQ_IMP" "EQ_CLAUSES" "NOT_CLAUSES_WEAK" "AND_CLAUSES"
   "OR_CLAUSES" "IMP_CLAUSES" "IMP_EQ_CLAUSE" "EXISTS_UNIQUE_THM" "EXISTS_REFL"
   "EXISTS_UNIQUE_REFL" "UNWIND_THM1" "UNWIND_THM2" "FORALL_UNWIND_THM2" "FORALL_UNWIND_THM1"
   "SWAP_FORALL_THM" "SWAP_EXISTS_THM" "FORALL_AND_THM" "AND_FORALL_THM" "LEFT_AND_FORALL_THM"
   "RIGHT_AND_FORALL_THM" "EXISTS_OR_THM" "OR_EXISTS_THM" "LEFT_OR_EXISTS_THM" "RIGHT_OR_EXISTS_THM"
   "LEFT_EXISTS_AND_THM" "RIGHT_EXISTS_AND_THM" "TRIV_EXISTS_AND_THM" 
   "LEFT_AND_EXISTS_THM" "RIGHT_AND_EXISTS_THM"
   "TRIV_AND_EXISTS_THM" "TRIV_FORALL_OR_THM" 
   "TRIV_OR_FORALL_THM" "RIGHT_IMP_FORALL_THM" "RIGHT_FORALL_IMP_THM"
   "LEFT_IMP_EXISTS_THM" "LEFT_FORALL_IMP_THM" "TRIV_FORALL_IMP_THM" 
   "TRIV_EXISTS_IMP_THM" "EXISTS_UNIQUE_ALT" "EXISTS_UNIQUE")

 hol-light-tactics   
 '("ABS_TAC" "ACCEPT_TAC" "ALL_TAC" "ANTS_TAC" "AP_TERM_TAC"
   "AP_THM_TAC" "ASSUME_TAC" "BETA_TAC" "BINOP_TAC" "CHANGED_TAC"
   "CHEAT_TAC" "CHOOSE_TAC" "CONJ_TAC" "CONTR_TAC" "CONV_TAC"
   "DISCARD_TAC" "DISCH_TAC" "DISJ1_TAC" "DISJ2_TAC" "DISJ_CASES_TAC"
   "EQ_TAC" "EXISTS_TAC" "FAIL_TAC" "GEN_TAC" "LABEL_TAC"
   "MATCH_ACCEPT_TAC" "MATCH_MP_TAC " "META_EXISTS_TAC" "META_SPEC_TAC" "MK_COMB_TAC"
   "MP_TAC" "NO_TAC" "RECALL_ACCEPT_TAC" "REFL_TAC" "REPLICATE_TAC"
   "RULE_ASSUM_TAC " "SPEC_TAC" "STRIP_ASSUME_TAC" "STRIP_GOAL_THEN" "STRIP_TAC"
   "STRUCT_CASES_TAC" "SUBGOAL_TAC" "SUBST1_TAC" "SUBST_ALL_TAC" "SUBST_VAR_TAC"
   "UNDISCH_TAC" "X_CHOOSE_TAC" "X_GEN_TAC" "X_META_EXISTS_TAC")

 hol-light-tacticals 
 '("ORELSE" "FIRST" "CHANGED_TAC" "THEN" "THENL" 
   "EVERY" "REPEAT" "MAP_EVERY"
   "IMP_RES_THEN"
   "FIND_ASSUM" "POP_ASSUM" "ASSUM_LIST" "EVERY_ASSUM" "FIRST_ASSUM"
   "CONJUCTS_THEN" "DISJ_CASES_THEN" "DISCH_THEN" "X_CHOOSE_THEN" "MAP_EVERY"
   "CHOOSE_THEN" "STRIP_THM_THEN" "SUBGOAL_THEN" "FREEZE_THEN")

 proof-script-font-lock-keywords
 (append
  caml-font-lock-keywords
  (list
   (cons (proof-ids-to-regexp hol-light-keywords) 'font-lock-keyword-face)
   (cons (proof-ids-to-regexp hol-light-tactics) 'proof-tactics-name-face)
   (cons (proof-ids-to-regexp hol-light-rules) 'font-lock-keyword-face)
   (cons (proof-ids-to-regexp hol-light-tacticals) 'proof-tacticals-name-face)))

 ;;
 ;; Some decoration of the goals output [FIXME: not yet HOL Light]
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

 ;;
 ;; Some decoration of the response output
 ;;
 proof-goals-font-lock-keywords
 (setq 
  proof-goals-font-lock-keywords
  (list
   ;; Help system output
   (cons (proof-ids-to-regexp 
	  '("^----------[-]+$"
	    "SYNOPSIS" "DESCRIPTION" "FAILURE CONDITIONS"
	    "EXAMPLES" "SEE ALSO"))
	 'font-lock-keyword-face)
   (cons ": GoalstackPure.goalstack" 'proof-boring-face)
   (cons ": GoalstackPure.proofs"    'proof-boring-face)
   (cons ": Thm.thm"		    'proof-boring-face)
   (cons "val it ="		    'proof-boring-face)))

 ;; End of easy config.
 )


;;;
;;; Prooftree configuration  (experimental, ongoing)
;;;

;; regexps for recognising additional markup in output

(defvar hol-light-update-goal-regexp 
  (concat "\\[Goal ID \\([0-9]+\\)\\]"
	  "\\s-*\n\\(\\(?:.+\n\\)*\\)\\(?:\n\\|$\\)"))

(defconst hol-light-current-goal-regexp
  ;; match final (focused) subgoal.  
  (concat (regexp-quote "[*]") 
	  "\\[Goal ID \\([0-9]+\\)\\]"
	  "\\s-*\n\\(\\(?:.+\n\\)*\\)\\(?:\n\\|$\\)"))
	  
(defconst hol-light-additional-subgoal-regexp 
  "\\[New Goal IDs: \\([0-9 ]+\\)\\]"
  "HOL Light instance of `proof-tree-additional-subgoal-ID-regexp'.")

(defconst hol-light-statenumber-regexp 
  "<prompt>\\([0-9]+\\)|\\([0-9]+\\)</prompt>"
  "Regular expression to match prompt with state numbers.
The first number is a global state counter which increases with
processed steps.  The second number is the number of steps within
the currently open proof.")

(defconst hol-light-existential-regexp "\\(\\?[0-9]+\\)"
  "Regexp for `proof-tree-existential-regexp'.")

(defconst hol-light-existentials-state-start-regexp "^(dependent evars:"
  "HOL Light instance of `proof-tree-existentials-state-start-regexp'.")

(defconst hol-light-existentials-state-end-regexp ")\n"
  "HOL Light instance of `proof-tree-existentials-state-end-regexp'.")


(setq 
 ;; These ones belong in script mode config
 proof-tree-configured t
 proof-tree-get-proof-info 'hol-light-get-proof-info
 proof-tree-find-begin-of-unfinished-proof 
           'hol-light-find-begin-of-unfinished-proof
 ;; These ones belong in shell mode
 proof-tree-proof-finished-regexp "No subgoals"	  
 proof-tree-show-sequent-command 
 (lambda (id) (format "print_xgoal_of_id \"%s\";;" id))

 proof-tree-current-goal-regexp hol-light-current-goal-regexp
 proof-tree-additional-subgoal-ID-regexp hol-light-additional-subgoal-regexp
 proof-tree-update-goal-regexp hol-light-update-goal-regexp
 proof-tree-cheating-regexp "CHEAT_TAC" ;; others...

 proof-tree-existential-regexp hol-light-existential-regexp
 proof-tree-existentials-state-start-regexp hol-light-existentials-state-start-regexp
 proof-tree-existentials-state-end-regexp hol-light-existentials-state-end-regexp
 ) ;; end setq proof tree stuff



;;; get proof info: uses last goals output
;;; FIXME problem here: this is called BEFORE last goals output 
;;; is set.  Can we move order without harming Coq?

;; TEMP to fix compile.  Will use Coq-stype annotated prompt for proof tree now.
(defvar proof-shell-delayed-output-start nil)
(defvar proof-shell-delayed-output-end nil)
(defvar proof-info nil)
(defvar proof-action-list nil)
(defun proof-shell-action-list-item (&rest args))

(defconst hol-light-show-sequent-command "print_xgoal_of_id %s;;")

(defun hol-light-get-proof-info ()
  "Return proof info for Prooftree for HOL Light.
See `proof-tree-get-proof-info'."
  (let ((proof-state-number 0)
	(proof-name         "Goal")) ; no named goals

    (when (and t ; (> proof-nesting-depth 0) ; inside a proof
	       (string-match hol-light-statenumber-regexp 
		proof-shell-last-prompt))
      (setq proof-state-number 
	    (string-to-number 
	     (match-string 1 proof-shell-last-prompt))))
    (list 
     proof-state-number
     proof-name)))

(defun hol-light-find-begin-of-unfinished-proof ()
  ;; Quick hack, we should use some internal proof script stuff here
  (save-excursion
    (re-search-backward "^g" nil t)))


;;; FIXME: this is duplicated from coq.el.  It might be kind of generic.
;;; However, for HOL Light the default behaviour is actually to print out
;;; exactly the new subgoals arising from a previous tactic allocation,
;;; or the currently focused goal (top of stack).

(defun hol-light-proof-tree-get-new-subgoals ()
  "Check for new subgoals and issue appropriate Show commands.
This is a hook function for `proof-tree-urgent-action-hook'. This
function examines the current goal output and searches for new
unknown subgoals. Those subgoals have been generated by the last
proof command and we must send their complete sequent text
eventually to prooftree. Because subgoals may change with
the next proof command, we must execute the additionally needed
Show commands before the next real proof command.

The ID's of the open goals are checked with
`proof-tree-sequent-hash' in order to find out if they are new.
For any new goal an appropriate Show Goal command with a
'proof-tree-show-subgoal flag is inserted into
`proof-action-list'. Then, in the normal delayed output
processing, the sequent text is send to prooftree as a sequent
update (see `proof-tree-update-sequent') and the ID of the
sequent is registered as known in `proof-tree-sequent-hash'.

The not yet delayed output is in the region
\[proof-shell-delayed-output-start, proof-shell-delayed-output-end]."
  ;; (message "CPTGNS start %s end %s"
  ;;          proof-shell-delayed-output-start
  ;;          proof-shell-delayed-output-end)
  (with-current-buffer proof-shell-buffer
    (let ((start proof-shell-delayed-output-start)
          (end proof-shell-delayed-output-end))
      (goto-char start)
      (while (proof-re-search-forward
              hol-light-update-goal-regexp end t)
        (let ((subgoal-id (match-string-no-properties 1)))
          (unless (gethash subgoal-id proof-tree-sequent-hash)
            (setq proof-action-list
                  (cons (proof-shell-action-list-item
                         (format hol-light-show-sequent-command subgoal-id)
                         (proof-tree-make-show-goal-callback (car proof-info))
                         '(no-goals-display
                           no-response-display
                           proof-tree-show-subgoal))
                        proof-action-list))))))))
  
(add-hook 'proof-tree-urgent-action-hook 'hol-light-proof-tree-get-new-subgoals)


;;;
;;; Menu commands
;;;

(proof-definvisible hol-light-dump-proof "dump_proof();;")

(defpgdefault menu-entries
  '(["Dump refactored proof" hol-light-dump-proof t]))

(provide 'hol-light)
