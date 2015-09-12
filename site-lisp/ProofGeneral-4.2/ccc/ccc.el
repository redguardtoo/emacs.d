;; ccc.el - Proof General for the Casl Consistency Checker
;;
;; Author: Christoph Lüth <cxl@informatik.uni-bremen.de>
;;
;; This is a fairly straightforward instantiation of Proof General for
;; the Casl Consistency Checker, CCC.
;;
;; CASL is the standard algebraic specification language, and CCC is a
;; tool to check consistency of CASL specifications.
;;
;; For more information, hasten thee browser yonder:
;;   http://www.informatik.uni-bremen.de/cofi/ccc

(require 'proof-easy-config)            ; nice and easy does it
(require 'proof-syntax)			; functions for making regexps

(defvar ccc-keywords nil)
(defvar ccc-tactics nil)
(defvar ccc-tacticals nil)

(proof-easy-config  'ccc "CASL Consistency Checker"
 proof-prog-name		 "ccc" ;; must be in your path.
 proof-terminal-string             ";"
 proof-script-comment-start      "(*"
 proof-script-comment-end        "*)"
 proof-goal-command-regexp       "\\(ccc\\|holcasl\\) \".*\";"
 proof-save-command-regexp       "^qeccc"
 proof-goal-with-hole-regexp     "\\(ccc\\|holcasl\\) \"\\(\\(.*\\)\\)\""
 proof-save-with-hole-regexp     "qeccc \"\\(\\(.*\\)\\)\""
 proof-non-undoables-regexp      "undo\\|back"
 proof-goal-command              "ccc \"%s\";"
 proof-save-command              "qeccc \"%s\";"
 proof-kill-goal-command         "abort ();"
 proof-showproof-command         "prt()"
 proof-undo-n-times-cmd          "undo_steps %s;"
 proof-auto-multiple-files       nil
 proof-shell-cd-cmd              "cd \"%s\""
 proof-shell-interrupt-regexp    "Interrupt"
 proof-shell-start-goals-regexp  "^No subgoals\\|^[0-9]* subgoals\\|^Wts:"
 proof-shell-end-goals-regexp    "val it"
 proof-shell-quit-cmd            "quit();"
 proof-assistant-home-page       "http://www.informatik.uni-bremen.de/cofi/tools/ccc"
 proof-shell-annotated-prompt-regexp  "^\\(val it = () : unit\n\\)?\\(CCC\\|^HOL-CASL\\)> " ;; "^\\(val it = () : unit\n\\)?ML>? "
 proof-shell-error-regexp        "\\*\\*\\*\\|^.*Error:\\|^uncaught exception \\|^Exception- "
 proof-shell-proof-completed-regexp "^Consistency proof successfully finished."
 proof-shell-eager-annotation-start "^\\[opening \\|^###\\|^Reading" ;;; ???

 ;;
 ;; Some basic fontlocking and syntax table entries, as taken from the
 ;; hol98 instance (it's all SML anyway :-)
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
   ?\[ "(]"
   ?\] ")["
   ?\* ". 23"
   ?\( "()1"
   ?\) ")(4")

 ccc-keywords  '("use" "ap" "holcasl" "ccc" "load_lib" "qeccc")
 ccc-tactics   '("compose" "compose'" "prove" "prove_free_type")
 ccc-tacticals '("Repeat" "Orelse" "Then" "ThenList" "OrelseList")
 proof-script-font-lock-keywords
 (list
  (cons (proof-ids-to-regexp ccc-keywords) 'font-lock-keyword-face)
  (cons (proof-ids-to-regexp ccc-tactics) 'font-lock-keyword-face)
  ; (cons (proof-ids-to-regexp hol98-rules) 'font-lock-keyword-face)
  (cons (proof-ids-to-regexp ccc-tacticals) 'proof-tacticals-name-face))


)
