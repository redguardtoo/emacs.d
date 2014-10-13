;; demoisa.el Example Proof General instance for Isabelle
;;
;; Copyright (C) 1999 LFCS Edinburgh.
;;
;; Author: David Aspinall <David.Aspinall@ed.ac.uk>
;;
;; demoisa.el,v 12.0 2011/10/13 10:54:51 da Exp
;;
;; =================================================================
;;
;; See README in this directory for an introduction.
;;
;; NEW INSTANCES: please use demoisa-easy.el as a basis instead.
;;
;; Basic configuration is controlled by one line in `proof-site.el'.
;; It has this line in proof-assistant-table:
;;
;;     (demoisa "Isabelle Demo"	"\\.ML$")
;;
;; From this it loads this file "demoisa/demoisa.el" whenever
;; a .ML file is visited, and sets the mode to `demoisa-mode'
;; (defined below).
;;
;; I've called this instance "Isabelle Demo Proof General" just to
;; avoid confusion with the real "Isabelle Proof General" in case the
;; demo gets loaded by accident.
;;
;; To make the line above take precedence over the real Isabelle mode
;; later in the table, set PROOFGENERAL_ASSISTANTS=demoisa in the
;; shell before starting Emacs	(or customize proof-assistants).
;;

(require 'proof)			; load generic parts
(require 'pg-goals)
(require 'pg-response)


;; ======== User settings for Isabelle ========
;;
;; Defining variables using customize is pretty easy.
;; You should do it at least for your prover-specific user options.
;;
;; proof-site provides us with two customization groups
;; automatically:  (based on the name of the assistant)
;;
;; 'isabelledemo	-  User options for Isabelle Demo Proof General
;; 'isabelledemo-config -  Configuration of Isabelle Proof General
;;			   (constants, but may be nice to tweak)
;;
;; The first group appears in the menu
;;   ProofGeneral -> Customize -> Isabelledemo
;; The second group appears in the menu:
;;   ProofGeneral -> Internals -> Isabelledemo config
;;

(defcustom isabelledemo-prog-name "isabelle"
  "*Name of program to run Isabelle."
  :type 'file
  :group 'isabelledemo)

(defcustom isabelledemo-web-page
  "http://www.cl.cam.ac.uk/Research/HVG/isabelle.html"
  "URL of web page for Isabelle."
  :type 'string
  :group 'isabelledemo-config)


;;
;; ======== Configuration of generic modes ========
;;

(defun demoisa-config ()
  "Configure Proof General scripting for Isabelle."
  (setq
   proof-terminal-string	";"
   proof-script-comment-start	"(*"
   proof-script-comment-end	"*)"
   proof-goal-command-regexp	"^Goal"
   proof-save-command-regexp	"^qed"
   proof-goal-with-hole-regexp	"qed_goal \"\\(\\(.*\\)\\)\""
   proof-save-with-hole-regexp	"qed \"\\(\\(.*\\)\\)\""
   proof-non-undoables-regexp	"undo\\|back"
   proof-undo-n-times-cmd	"pg_repeat undo %s;"
   proof-showproof-command	"pr()"
   proof-goal-command		"Goal \"%s\";"
   proof-save-command		"qed \"%s\";"
   proof-kill-goal-command	"Goal \"PROP no_goal_set\";"
   proof-assistant-home-page	isabelledemo-web-page
   proof-prog-name		isabelledemo-prog-name
   proof-auto-multiple-files	t))


(defun demoisa-shell-config ()
  "Configure Proof General shell for Isabelle."
  (setq
   proof-shell-annotated-prompt-regexp	 "^\\(val it = () : unit\n\\)?\\(ML\\)?> "
   proof-shell-cd-cmd			"cd \"%s\""
   proof-shell-interrupt-regexp		"Interrupt"
   proof-shell-error-regexp		"\\*\\*\\*\\|^.*Error:\\|^uncaught exception \\|^Exception- "
   proof-shell-start-goals-regexp	"Level [0-9]"
   proof-shell-end-goals-regexp		"val it"
   proof-shell-proof-completed-regexp	"^No subgoals!"
   proof-shell-eager-annotation-start	"^\\[opening \\|^###\\|^Reading"
   proof-shell-init-cmd	 ; define a utility function, in a lib somewhere?
   "fun pg_repeat f 0 = ()
      | pg_repeat f n = (f(); pg_repeat f (n-1));"
   proof-shell-quit-cmd			"quit();"))



;;
;; ======== Defining the derived modes ========
;;

;; The derived modes set the variables, then call the
;; <mode>-config-done function to complete configuration.

(define-derived-mode demoisa-mode proof-mode
    "Isabelle Demo script" nil
    (demoisa-config)
    (proof-config-done))

(define-derived-mode demoisa-shell-mode proof-shell-mode
   "Isabelle Demo shell" nil
   (demoisa-shell-config)
   (proof-shell-config-done))

(define-derived-mode demoisa-response-mode proof-response-mode
  "Isabelle Demo response" nil
  (proof-response-config-done))

(define-derived-mode demoisa-goals-mode proof-goals-mode
  "Isabelle Demo goals" nil
  (proof-goals-config-done))

;; A more sophisticated instantiation might set font-lock-keywords to
;; add highlighting, or some of the proof by pointing markup
;; configuration for the goals buffer.

(provide 'demoisa)
