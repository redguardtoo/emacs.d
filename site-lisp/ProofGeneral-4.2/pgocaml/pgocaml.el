;; pgocaml.el - Proof General for OCaml scripts.
;;
;; David Aspinall.  pgocaml.el,v 1.1 2012/02/07 11:19:42 da Exp
;;
;; This instance of PG is handy just for using script management to
;; cut-and-paste into a buffer running OCaml
;;
;; I'm providing this so that tool demonstrators may use it instead of
;; tediously doing cut-and-paste of commands from a file.  No history
;; management, and nothing to do with theorem proving really!
;;
;; To use this instance of PG, visit a file with the ".pgml" extension
;; or type
;;
;;  M-x pgocaml-mode
;;
;; in an ordinary .ml file.  (Check that you have enabled the instance
;; in proof-site.el).
;;


(require 'proof-easy-config)
(require 'proof-syntax)

(proof-easy-config 'pgocaml "PG-OCaml"

 proof-prog-name		     "ocaml"
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

(provide 'pgocaml)
