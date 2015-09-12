;; pgocaml.el - Proof General for Haskell scripts.
;;
;; David Aspinall.  pghaskell.el,v 1.2 2012/08/09 11:43:02 da Exp
;;
;; This instance of PG is handy just for using script management to
;; cut-and-paste into a buffer running Haskell (ghci)
;;
;; I'm providing this so that tool demonstrators may use it instead of
;; tediously doing cut-and-paste of commands from a file.  No history
;; management, and nothing to do with theorem proving really!
;;
;; To use this instance of PG, visit a file with the ".pghci" extension
;; or type
;;
;;  M-x pghaskell-mode
;;
;; in an ordinary .h file.  (Check that you have enabled the instance
;; in proof-site.el).
;;


(require 'proof-easy-config)
(require 'proof-syntax)

(proof-easy-config 'pghaskell "PG-Haskell"

 proof-prog-name		     "ghci"

;; BELOW HERE TO COMPLETE

 proof-terminal-string               ";;"
 proof-script-comment-start          "(*"
 proof-script-comment-end            "*)"
 proof-shell-annotated-prompt-regexp "^# "  ;; matches interpreter prompts

 ;; Syntax table suitable for OCaml; see Elisp documentation of `modify-syntax-entry'
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

 ;; next setting is just to prevent warning
 proof-save-command-regexp	proof-no-regexp
 )

(provide 'pghaskell)
