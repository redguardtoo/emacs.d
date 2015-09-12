;; pgshell.el - Proof General for shell scripts.
;;
;; David Aspinall.  pgshell.el,v 12.0 2011/10/13 10:54:51 da Exp
;;
;; This instance of PG is handy just for using script management to
;; cut-and-paste into a buffer running an ordinary shell of some kind.
;;
;; I'm providing this so that tool demonstrators may use it instead of
;; tediously doing cut-and-paste of commands from a file.  No history
;; management, and nothing to do with theorem proving really!
;;
;; To use this instance of PG, visit a file with the ".pgsh" extension.
;;
;; Feedback welcome.


(require 'proof-easy-config)
(require 'proof-syntax)

(proof-easy-config 'pgshell "PG-Shell"

 proof-prog-name		     "/bin/sh"  ;; or your program
 proof-terminal-string                 ";"        ;; end of commands
 proof-script-comment-start          "\#"	;; comments
 proof-shell-annotated-prompt-regexp "^.*[$] $" ;; matches prompts

 proof-script-fly-past-comments  t	        ;; nice for single-line

 ;; Syntax table gets font-locking and editing features for comments.
 ;; see Elisp documentation of `modify-syntax-entry'
 proof-script-syntax-table-entries '(?\# "<" ?\n ">")

 ;; next setting is just to prevent warning
 proof-save-command-regexp	proof-no-regexp
 )

(provide 'pgshell)
