;; Lexer.
;; - We distinguish ":=" from ":= inductive" to avoid the circular precedence
;;   constraint ":= < | < ; < :=" where ":= < |" is due to Inductive
;;   definitions, "| < ;" is due to tactics precedence, "; < :=" is due to
;;   "let x:=3; y:=4 in...".
;; - We distinguish the ".-selector" from the terminator "." for
;;   obvious reasons.
;; - We consider qualified.names as one single token for obvious reasons.
;; - We distinguish the "Module M." from "Module M := exp." since the first
;;   opens a new scope (closed by End) whereas the other doesn't.
;; - We drop "Program" because it's easier to consider "Program Function"
;;   as a single token (which behaves like "Function" w.r.t indentation and
;;   parsing) than to get the parser to handle it correctly.
;; - We identify the different types of bullets (First approximation).
;; - We distinguish "with match" from other "with".

(require 'coq-indent)
(require 'smie nil 'noerror)

;; each element should end with "."
(defconst coq-smie-dot-friends '("*." "-*." "|-*." "*|-*." ":?."))
;; this captures ".." which not desirable
;(defconst coq-smie-dot-friends-regexp "\\s_*\\.")

; for debuging
(defun coq-time-indent ()
  (interactive)
  (let ((deb (float-time)))
    (smie-indent-line)
    (message "time: %S"(- (float-time) deb))))

(defun coq-time-indent-region (beg end)
  (interactive "r")
  (let ((deb (float-time)))
    (indent-region beg end nil)
    (message "time: %S"(- (float-time) deb))))




(defun coq-smie-is-tactic ()
  (save-excursion
    (coq-find-real-start)
    (let ((cfs case-fold-search))
      (setq case-fold-search nil)
      (let ((res (looking-at "[[:upper:]]")))
	(setq case-fold-search cfs)
	(not res)))))


(defun coq-smie-.-deambiguate ()
  "Return the token of the command terminator of the current command.
For example in:

Proof.

the token of the \".\" is \". proofstart\".

But in

intros.

the token of \".\" is simply \".\".
"
  (save-excursion
    (let ((p (point)) (beg (coq-find-real-start))) ; moves to real start of command
      (cond
       ((looking-at "Proof\\>\\|BeginSubproof\\>") ". proofstart")
       ((or (looking-at "Next\\s-+Obligation\\>")
	    (coq-smie-detect-goal-command))
	(save-excursion
	  (goto-char (+ p 1))
	  (if (equal (smie-default-forward-token) "Proof")
	      "." ". proofstart")))
       ((equal (coq-smie-module-deambiguate) "Module start")
	". modulestart")
       (t ".")))))


(defun coq-smie-complete-qualid-backward ()
  "Return the qualid finishing at the current point."
  (let ((p (point)))
    (re-search-backward "[^.[:alnum:]_@]")
    (forward-char 1)
    (buffer-substring (point) p)))


(defun coq-smie-find-unclosed-match-backward ()
  (let ((tok (coq-smie-search-token-backward '("with" "match" "."))))
    (cond
     ((null tok) nil)
     ((equal tok ".") nil)
     ((equal tok "match") t)
     ((equal tok "with")
      (coq-smie-find-unclosed-match-backward)
      (coq-smie-find-unclosed-match-backward)))))

(defun coq-smie-with-deambiguate()
  (let ((p (point)))
    (if (coq-smie-find-unclosed-match-backward)
	"with match"
      (goto-char p)
      (coq-find-real-start)
      (cond
       ((looking-at "Inductive") "with inductive")
       ((looking-at "Fixpoint\\|Function\\|Program") "with fixpoint")
       ((looking-at "Module\\|Declare") "with module")
       (t "with")))))




;; ignore-between is a description of pseudo delimiters of blocks that
;; should be jumped when searching. There is a bad interaction when
;; tokens and ignore-bteween are not disjoint
(defun coq-smie-search-token-forward (tokens &optional end ignore-between)
  "Search for one of TOKENS between point and END.
If some enclosing parenthesis is reached, stop there and return
nil. Token \".\" is considered only if followed by a space.
optional IGNORE-BETWEEN defines opener/closer to ignore during
search. Careful: the search for a opener stays inside the current
command (and inside parenthesis)."
  (unless end (setq end (point-max)))
  (condition-case nil
      (catch 'found
	(while (< (point) end)
	  ;; The default lexer is faster and is good enough for our needs.
	  (let* ((next2 (smie-default-forward-token))
		 (is-dot-friend (member next2 coq-smie-dot-friends))
		 (next (if is-dot-friend "." next2))
		 (parop (assoc next ignore-between)))
	    ; if we find something to ignore, we directly jump to the
	    ; corresponding closer
	    (if parop
		(let ((parops ; corresponding matcher may be a list
		       (if (listp parop) (cdr parop)
			 (cons (cdr parop) nil)))) ; go to corresponding closer
		  (when (member
			 (coq-smie-search-token-forward
			  (append parops (cons "." nil))
			  end ignore-between)
			 (cons "." nil)) ;coq-smie-dot-friends
		  (goto-char (point))
		  next))
	      ;; Do not consider "." when not followed by a space
	      (when (or (not (equal next ".")) ; see backward version
			(looking-at "[[:space:]]"))
		(cond
		 ((and (zerop (length next))
		       (or (equal (point) (point-max)) ; protecting char-after next line
			   (equal (char-syntax ?\)) (char-syntax (char-after)))))
		  (throw 'found nil))
		 ((zerop (length next)) ;; capture other characters than closing parent
		  (forward-sexp 1))
		 ((member next tokens) (throw 'found next))))))))
    (scan-error nil)))

;; ignore-between is a description of pseudo delimiters of blocks that
;; should be jumped when searching. There is a bad interaction when
;; tokens and ignore-bteween are not disjoint
(defun coq-smie-search-token-backward (tokens &optional end ignore-between)
  "Search for one of TOKENS between point and END.
If some enclosing parenthesis is reached, stop there and return
nil. Token \".\" is considered only if followed by a space.
optional IGNORE-BETWEEN defines opener/closer to ignore during
search. Careful: the search for a opener stays inside the current
command (and inside parenthesis). "
  (unless end (setq end (point-min)))
    (condition-case nil
	(catch 'found
	  (while (> (point) end)
	    ;; The default lexer is faster and is good enough for our needs.
	    (let* ((next2 (smie-default-backward-token))
		   (is-dot-friend (member next2 coq-smie-dot-friends))
		   (next (if is-dot-friend "." next2))
		   (parop (rassoc next ignore-between)))
	      ; if we find something to ignore, we directly jump to the
	      ; corresponding openner
	      (if parop
		  (let ((p (point))
			(parops ; corresponding matcher may be a list
			 (if (listp (car parop)) (car parop) (cons (car parop) nil))))
		    ; go to corresponding closer or meet "."
		    ;(message "newpatterns = %S" (append parops (cons "." nil)))
		    (when (member
			   (coq-smie-search-token-backward
			    (append parops (cons "." nil)) ;coq-smie-dot-friends
			    end ignore-between)
			   (cons "." nil)) ;coq-smie-dot-friends
		      (goto-char (point))
		      next))
		;; Do not consider "." when not followed by a space
		;(message "SPACE?: %S , %S , %S" next2 next (looking-at ".[[:space:]]"))
		(when (or (not (equal next2 "."))
			  (looking-at "\\.[[:space:]]"))
		  (cond
		   ((and (zerop (length next))
			 (or (equal (point) (point-min)) ; protecting char-before next line
			     (equal (char-syntax ?\() (char-syntax (char-before)))))
		    (throw 'found nil))
		   ((zerop (length next)) (forward-sexp -1))
		   ((member next tokens) (throw 'found next))))))))
      (scan-error nil)))

(defun coq-lonely-:=-in-this-command ()
  "Return t if there is a lonely \":=\" from (point) to end of command.
Non lonely \":=\" are those corresponding to \"let\" or
\"with\" (module declaration) or those inside parenthesis. this
function is used to detect whether a command is a definition or a
proof-mode starter in Coq."
  (equal (coq-smie-search-token-forward
	  '("." ":=") nil
	  '(("with" . (":=" "signature")) ("let" . "in")))
	 "."))

;; Heuristic to detect a goal opening command: there must be a lonely
;; ":=" until command end.
;; \\|\\(Declare\\s-+\\)?Instance is not detected as it is not
;; syntactically decidable to know if some goals are created. Same for
;; Program Fixpoint but with Program Next Obligation is mandatory for
;; each goal.
(defun coq-smie-detect-goal-command ()
  "Return t if the next command is a goal starting to be indented.
The point should be at the beginning of the command name. As
false positive are more annoying than false negative, return t
only if it is FOR SURE a goal opener. Put a \"Proof.\" when you want to
force indentation."
  (save-excursion ; FIXME add other commands that potentialy open goals
    (when (proof-looking-at "\\(Local\\|Global\\)?\
\\(Definition\\|Lemma\\|Theorem\\|Fact\\|Let\\|Class\
\\|Add\\(\\s-+Parametric\\)?\\s-+Morphism\\)\\>")
	(coq-lonely-:=-in-this-command))))


;; Heuristic to detect a goal opening command: there must be a lonely ":="
(defun coq-smie-module-deambiguate ()
  "Return t if the next command is a goal starting command.
The point should be at the beginning of the command name."
  (save-excursion ; FIXME Is there other module starting commands?
    (cond
     ((looking-back "with\\s-+") "module") ; lowecase means Module that is not a declaration keyword (like in with Module) 
     ((proof-looking-at "\\(Module\\|Section\\)\\>")
      (if (coq-lonely-:=-in-this-command) "Module start" "Module def")))))


;(defun coq-smie-detect-module-or-section-start-command ()
;  "Return t if the next command is a goal starting command.
;The point should be at the beginning of the command name."
;  (save-excursion ; FIXME Is there other module starting commands?
;    (when (and (looking-back "with")
;	       (proof-looking-at "\\(\\(?:Declare\\s-+\\)?Module\\|Section\\)\\>"))
;      (coq-lonely-:=-in-this-command))))


(defconst coq-smie-proof-end-tokens
  ;; '("Qed" "Save" "Defined" "Admitted" "Abort")
  (cons "EndSubproof" (remove "End" coq-keywords-save-strict)))

(defun coq-smie-forward-token ()
  (let ((tok (smie-default-forward-token)))
    (cond
     ;; @ may be  ahead of an id, it is part of the id.
     ((and (equal tok "@") (looking-at "[[:alpha:]_]"))
      (let ((newtok (coq-smie-forward-token))) ;; recursive call
	(concat tok newtok)))
     ;; detecting if some qualification (dot notation) follows that id and
     ;; extend it if yes. Does not capture other alphanumerical token (captured
     ;; below)
     ((and (string-match "@?[[:alpha:]_][[:word:]]*" tok)
	   (looking-at "\\.[[:alpha:]_]")
	   (progn (forward-char 1)
		  (let ((newtok (coq-smie-forward-token))) ; recursive call
		    (concat tok "." newtok)))))
     ((member tok '("." "..."))
      ;; swallow if qualid, call backward-token otherwise
      (cond
       ((member (char-after) '(?w ?_))  ;(looking-at "[[:alpha:]_]") ;; extend qualifier
	(let ((newtok (coq-smie-forward-token))) ;; recursive call
	  (concat tok newtok)))
       (t (save-excursion (coq-smie-backward-token))))) ;; recursive call
     ((member tok
	      '("=>" ":=" "+" "-" "*" "exists" "in" "as" "∀" "∃" "→" ";" "," ":" "eval"))
      ;; The important lexer for indentation's performance is the backward
      ;; lexer, so for the forward lexer we delegate to the backward one when
      ;; we can.
      (save-excursion (coq-smie-backward-token)))

     ;; detect "with signature", otherwies use coq-smie-backward-token
     ((equal tok "with")
      (let ((p (point)))
	(if (equal (smie-default-forward-token) "signature")
	    "with signature"
	  (goto-char p)
	  (save-excursion (coq-smie-backward-token)))))

     ((member tok '("transitivity" "symmetry" "reflexivity"))
      (let ((p (point)))
	(if (and (equal (smie-default-forward-token) "proved")
		 (equal (smie-default-forward-token) "by"))
	    "xxx provedby"
	  (goto-char p)
	  tok))) ; by tactical

     ((member tok '("Module")) ; TODO: Declare
      (let ((pos (point))
	    (next (smie-default-forward-token)))
	(unless (equal next "Type") (goto-char pos))
	(save-excursion (coq-smie-backward-token))))

     ((member tok '("End"))
      (save-excursion (coq-smie-backward-token)))

     ((and (zerop (length tok)) (looking-at "{|")) (goto-char (match-end 0)) "{|")
     ;; this must be after detecting "{|":
     ((and (zerop (length tok)) (eq (char-after) ?\{))
      (if (equal (save-excursion (forward-char 1) (coq-smie-backward-token))
		 "{ subproof")
	  (progn (forward-char 1) "{ subproof")
	tok))
     ((and (zerop (length tok)) (eq (char-after) ?\}))
      (if (equal (save-excursion (forward-char 1)
				 (coq-smie-backward-token))
		 "} subproof")
	  (progn (forward-char 1) "} subproof")
	tok))
     ((and (equal tok "|") (eq (char-after) ?\}))
      (goto-char (1+ (point))) "|}")
     ((member tok coq-smie-proof-end-tokens) "Proof End")
     ((member tok '("Obligation")) "Proof")
     ((member tok coq-smie-dot-friends) ".")
     (tok))))


(defun coq-is-at-command-real-start()
  (equal (point)
	 (save-excursion (coq-find-real-start))))


(defun coq-smie-:=-deambiguate ()
  (let ((corresp (coq-smie-search-token-backward
		  '("let" "Inductive" "Coinductive" "{|" "." "with" "Module")
		  nil '((("let" "with") . ":=")))))
    (if (and (equal corresp "with") ; "as "with" belongs to the searched token we can't have it in excluded tokens
	     (equal (coq-smie-with-deambiguate) "with match"))
	(coq-smie-:=-deambiguate) ; recursive call if the with found is actually et with match
      (cond
       ((equal corresp ".") ":= def") ; := outside of any parenthesis
       ((equal corresp "Module")
	(let ((p (point)))
	  (if (equal (smie-default-backward-token) "with")
	      ":= with"
	    (goto-char p)
	    ":= module")))
       ((member corresp '("Inductive" "CoInductive")) ":= inductive"); := inductive
       ((equal corresp "let") ":= let")
       ((equal corresp "with") ":= with")
       ((or (looking-back "{")) ":= record")
       (t ":="))))) ; a parenthesis stopped the search
;
;     ((equal tok ":=")
;      (save-excursion
;	;(save-excursion (coq-smie-:=-deambiguate)); TODO
;	(let ((corresp (coq-smie-search-token-backward
;			'("let" "Inductive" "Coinductive" "{|" "." "with" "Module")
;			nil '((("let" "with") . ":="))))) ;("match" . "with")
;	  (cond
;	   ((member corresp '("Inductive" "CoInductive")) ":="); := inductive
;	   ((equal corresp "let") ":= let")
;	   ((equal corresp "with") ":= with")
;	   ((or (looking-back "{")) ":= record")
;	   (t tok)))))
;


(defun coq-smie-backward-token ()
  (let ((tok (smie-default-backward-token)))
    (cond
     ((equal tok ",")
      (save-excursion
	(let ((backtok (coq-smie-search-token-backward
			'("forall" "∀" "∃" "exists" "|" "match" "."))))
	  (cond
	   ((member backtok '("forall" "∀" "∃")) ", quantif")
	   ((equal backtok "exists") ; there is a tactic called exists
	    (if (equal (coq-smie-forward-token) ;; recursive call
		       "quantif exists")
		", quantif" tok))
	   (t tok)))))
     ;; Distinguish between "," from quantification and other uses of
     ;; "," (tuples, tactic arguments)

     ((equal tok ";")
      (save-excursion
	(let ((backtok (coq-smie-search-token-backward '("." "[" "{"))))
	  (cond
	   ((equal backtok ".") "; tactic")
	   ((equal backtok nil)
	    (if (or (looking-back "\\[")
		    (and (looking-back "{")
			 (equal (coq-smie-backward-token) "{ subproof"))) ;; recursive call
		"; tactic"
	      "; record"))))))

     ((equal tok "Module")
      (save-excursion
	;(coq-find-real-start)
	(coq-smie-module-deambiguate)))

     ;; rhaaa... Some peolple use "End" as a id...
     ((equal tok "End")
      (if (coq-is-at-command-real-start) "end module" tok))

     ((and (equal tok "|") (eq (char-before) ?\{))
      (goto-char (1- (point))) "{|")

     ((and (zerop (length tok)) (member (char-before) '(?\{ ?\}))
	   (save-excursion
	     (forward-char -1)
	     (member (coq-smie-backward-token) ;; recursive call
		     '("." ". proofstart" "{ subproof" "} subproof"
		     "- bullet" "+ bullet" "* bullet"))))
      (forward-char -1)
      (if (looking-at "{") "{ subproof" "} subproof"))

     ((and (equal tok ":") (looking-back "\\<\\(constr\\|ltac\\)"))
      ": ltacconstr")

     ((equal tok ":=")
      (save-excursion
	(save-excursion (coq-smie-:=-deambiguate))))
	;; (let ((corresp (coq-smie-search-token-backward
	;; 		'("let" "Inductive" "Coinductive" "{|" "." "with" "Module")
	;; 		nil '((("let" "with") . ":="))))) ;("match" . "with")
	;;   (cond
	;;    ((member corresp '("Inductive" "CoInductive")) ":="); := inductive
	;;    ((equal corresp "let") ":= let")
	;;    ((equal corresp "with") ":= with")
	;;    ((or (looking-back "{")) ":= record")
	;;    (t tok)))
	;; ))

     ((equal tok "=>")
      (save-excursion
	(let ((corresp (coq-smie-search-token-backward
			'("|" "match" "fun" ".")
			nil '(("match" . "end") ("fun" . "=>")))))
	  (cond
	   ((member corresp '("fun")) "=> fun") ; fun
	   (t tok)))))

     ;; FIXME: no token should end with "." except "." itself
     ; for "unfold in *|-*."
     ((member tok '("*." "-*." "|-*." "*|-*.")) (forward-char 1) ".")
     ; for "unfold in *|-*;"
     ((member tok '("*;" "-*;" "|-*;" "*|-*;")) (forward-char 1) "; tactic")
     ((and (member tok '("+" "-" "*"))
	   (save-excursion
	     (let ((prev (coq-smie-backward-token))) ;; recursive call
	       (member prev '("." ". proofstart" "{ subproof" "} subproof")))))
      (concat tok " bullet"))
     ((and (member tok '("exists" "∃"))
	   (save-excursion
	     (not (member
		   (coq-smie-backward-token) ;; recursive call
		   '("." ". proofstart" "; tactic" "[" "]" "|"
		     "{ subproof" "} subproof"))))
	   "quantif exists"))
     ((equal tok "∀") "forall")
     ((equal tok "→") "->")

     ((equal tok "with") ; "with" is a nightmare: at least 4 different uses
      (save-excursion (coq-smie-with-deambiguate)))

     ((and (equal tok "signature")
	   (equal (smie-default-backward-token) "with"))
      "with signature")

     ((equal tok "by")
      (let ((p (point)))
	(if (and (equal (smie-default-backward-token) "proved")
		 (member (smie-default-backward-token)
			 '("transitivity" "symmetry" "reflexivity")))
	    "xxx provedby"
	  (goto-char p)
	  tok))) ; by tactical

     ((equal tok "as")
      (save-excursion
	(let ((prev-interesting
	       (coq-smie-search-token-backward
		'("match" "Morphism" "Relation" "." ". proofstart"
		  "{ subproof" "} subproof" "as")
		nil
		'((("match" "let") . "with") ("with" . "signature")))))
	  (cond
	   ((equal prev-interesting "match") "as match")
	   ((member prev-interesting '("Morphism" "Relation")) "as morphism")
	   (t tok)))))

     ((equal tok "by")
      (let ((p (point)))
	(if (and (equal (smie-default-backward-token) "proved")
		 (member (smie-default-backward-token)
			 '("transitivity" "symmetry" "reflexivity")))
	    "xxx provedby"
	  (goto-char p)
	  tok))) ; by tactical


     ((equal tok "eval")
      (if (member (save-excursion
		    (forward-char 4)
		    (smie-default-forward-token))
		  '("red" "hnf" "compute" "simpl" "cbv" "lazy" "unfold" "fold" "pattern"))
	  "eval in" tok))
     

     ((equal tok "in")
      (save-excursion
	(let ((prev-interesting
	       (coq-smie-search-token-backward
		'("let" "match" ;"eval" should be "eval in" but this is not supported by search-token-backward
		  "." ) nil
		'(("match" . "with") (("let" ;"eval"
				       ) . "in")))))
	  (cond
	   ((member prev-interesting '("." nil)) "in tactic")
	   ((equal prev-interesting "let") "in let")
	   ;((equal prev-interesting "eval in") "in eval"); not detectable by coq-smie-search-token-backward
	   ((equal prev-interesting "match") "in match")
	   (t "in tactic")))))

      ((and (eq (char-before) ?@) (member (char-syntax (char-after)) '(?w ?_)))
       (forward-char -1)
       (concat "@" tok))

     ((member tok coq-smie-proof-end-tokens) "Proof End")

     ((member tok '("." "..."))
      ;; Distinguish field-selector "." from terminator "." from module
      ;; qualifier.
      (let ((nxtnxt (char-after (+ (point) (length tok)))))
	(if (eq nxtnxt ?\() ". selector"
	  (if (eq (char-syntax nxtnxt) ?\ )
	      ;; command terminator: ". proofstart" et al
	      (save-excursion (forward-char (- (length tok) 1))
			      (coq-smie-.-deambiguate))
	    (if (eq (char-syntax nxtnxt) ?w)
		(let ((newtok (coq-smie-complete-qualid-backward)))
		  ;; qualified name
		  (concat newtok tok))
	      ". selector")))))  ;; probably a user defined syntax

     ((and (and (eq (char-before) ?.) (member (char-syntax (char-after))
					      '(?w ?_))))
      (forward-char -1)
      (let ((newtok (coq-smie-backward-token))) ; recursive call
	(concat newtok "." tok)))

     ((member tok coq-smie-dot-friends) ".")

     (tok))))


(defcustom coq-indent-box-style nil
  "If non-nil, Coq mode will try to indent with a box style (SMIE code only).
Box style looke like this:
Lemma foo: forall n,
             n = n.

instead of

Lemma foo: forall n,
  n = n.
"
  :type 'boolean
  :group 'coq)


;; - TODO: remove tokens "{ subproof" and "} subproof" but they are
;;         needed by the lexers at a lot of places.
;; - FIXME: This does not know about Notations.
(defconst coq-smie-grammar
  (when (fboundp 'smie-prec2->grammar)
    (smie-prec2->grammar
     (smie-bnf->prec2
      '((exp
	 (exp ":= def" exp) (exp ":=" exp) (exp ":= inductive" exp)
	 (exp "|" exp) (exp "=>" exp)
	 (exp "xxx provedby" exp) (exp "as morphism" exp)
	 (exp "with signature" exp)
	 ("match" matchexp "with match" exp "end");expssss
	 ("let" assigns "in let" exp) ;("eval in" assigns "in eval" exp) disabled
	 ("fun" exp "=> fun" exp) ("if" exp "then" exp "else" exp)
	 ("quantif exists" exp ", quantif" exp)
	 ("forall" exp ", quantif" exp)
	 ;;;
	 ("(" exp ")") ("{|" exps "|}") ("{" exps "}")
	 (exp "; tactic" exp) (exp "in tactic" exp) (exp "as" exp)
	 (exp "by" exp) (exp "with" exp) (exp "|-" exp)
	 (exp ":" exp) (exp ":<" exp) (exp "," exp)
	 (exp "->" exp) (exp "<->" exp) (exp "/\\" exp) (exp "\\/" exp)
	 (exp "==" exp) (exp "=" exp) (exp "<>" exp) (exp "<=" exp)
	 (exp "<" exp) (exp ">=" exp) (exp ">" exp)
	 (exp "=?" exp) (exp "<=?" exp) (exp "<?" exp)
	 (exp "^" exp) (exp "+" exp) (exp "-" exp) (exp "*" exp)
	 (exp ": ltacconstr" exp)(exp ". selector" exp))
	;; Having "return" here rather than as a separate rule in `exp' causes
	;; it to be indented at a different level than "with".
	(matchexp (exp) (exp "as match" exp) (exp "in match" exp)
		  (exp "return" exp) )
	(exps (affectrec) (exps "; record" exps))
	(affectrec (exp ":= record" exp))
	(assigns  (exp ":= let" exp)) ;(assigns "; record" assigns)

	(moduledef (moduledecl ":= module" exp))
	(moduledecl (exp) (exp ":" moduleconstraint)
		    (exp "<:" moduleconstraint))
	(moduleconstraint
	 (exp) (exp ":= with" exp)
	 (moduleconstraint "with module" "module" moduleconstraint))

	(mutual (exp "with inductive" exp) (exp "with fixpoint" exp))

	;; To deal with indentation inside module declaration and inside
	;; proofs, we rely on the lexer. The lexer detects "." terminator of
	;; goal starter and returns the ". proofstart" and ". moduelstart"
	;; tokens.
	(bloc ("{ subproof" commands "} subproof")
	      (". proofstart" commands  "Proof End")
	      (". modulestart" commands  "end module" exp)
	      (moduledecl) (moduledef) (mutual) (exp))

	(commands (commands "." commands)
		  (commands "- bullet" commands)
		  (commands "+ bullet" commands)
		  (commands "* bullet" commands)
		  (bloc)))


      ;; Resolve the "trailing expression ambiguity" as in "else x -> b".
      ;; each line orders tokens by increasing priority
      ;; | C x => fun a => b | C2 x => ...
      ;;'((assoc "=>") (assoc "|")  (assoc "|-" "=> fun")) ; (assoc ", quantif")
      '((assoc "- bullet") (assoc "+ bullet") (assoc "* bullet") (assoc "."))
      '((assoc "with inductive")
	(assoc ":= def" ":= inductive") (assoc ":=") (assoc "|") (assoc "=>")
	(assoc "xxx provedby")
	(assoc "as morphism") (assoc "with signature") (assoc "with match")
	(assoc "in let")
	(assoc "in eval") (assoc "=> fun") (assoc "then") (assoc "else")
	(assoc ", quantif")
	(assoc "; tactic") (assoc "in tactic") (assoc "as" "by") (assoc "with")
	(assoc "|-") (assoc ":" ":<") (assoc ",") (assoc "->") (assoc "<->")
	(assoc "/\\") (assoc "\\/")
	(assoc "==") (assoc "=") (assoc "<" ">" "<=" ">=" "<>")
	(assoc "=?") (assoc "<=?") (assoc "<?") (assoc "^")
	(assoc "+") (assoc "-") (assoc "*")
	(assoc ": ltacconstr") (assoc ". selector") (assoc ""))
      '((assoc ":" ":<")  (assoc "<"))
      '((assoc ". modulestart" "." ". proofstart") (assoc "Module def")
	(assoc "with module" "module") (assoc ":= module")
	(assoc ":= with")  (assoc ":" ":<"))
      '((assoc ":= def") (assoc "; record") (assoc ":= record")))))
  "Parsing table for Coq.  See `smie-grammar'.")
;; FIXME:
; Record rec:Set :=     {
;                   fld1:nat;
;                   fld2:nat;
;                   fld3:bool
;                 }.
; FIXME: as is sometimes a "as morphism" but not detected as such
;; Add Parametric Morphism (A : Type) : (mu (A:=A))
;;     with signature Oeq ==> Oeq
;;                    as mu_eq_morphism.

;; FIXME: have a different token for := corresponding to a "fix"
;;Fixpoint join l : key -> elt -> t -> t :=
;;      match l with
;;        | Leaf => add
;;        | Node ll lx ld lr lh => fun x d =>
;;                                   fix join_aux (r:t) : t
;;        := match r with   <---- ??
;;             | Leaf =>  add x d l


; This fixes a bug in smie that is not yet in regular emacs distribs??
; To show the bug. Comment this and then try to indent the following:
; Module X.
; Module Y. <-- here -->  Error: (wrong-type-argument integer-or-marker-p nil)
; No need anymore?
;; (defun smie-indent--parent ()
;;   (or smie--parent
;;       (save-excursion
;; 	(let* ((pos (point))
;; 	       (tok (funcall smie-forward-token-function)))
;; 	  (unless (numberp (cadr (assoc tok smie-grammar)))
;; 	    (goto-char pos))
;; 	  (setq smie--parent
;; 		(or (smie-backward-sexp 'halfsexp)
;; 		    (let (res)
;; 		      (while (null (setq res (smie-backward-sexp))))
;; 		      (list nil (point) (nth 2 res)))))))))

(defun coq-smie-rules (kind token)
  "Indentation rules for Coq.  See `smie-rules-function'.
KIND is the situation and TOKEN is the thing w.r.t which the rule applies."
   (case kind
     (:elem (case token
	      (basic proof-indent)))
     (:list-intro
      (or (member token '("fun" "forall" "quantif exists"))
	  ;; We include "." in list-intro for the ". { .. } \n { .. }" so the
	  ;; second {..} is aligned with the first rather than being indented as
	  ;; if it were an argument to the first.
	  ;; FIXME: this gives a strange indentation for ". { \n .. } \n { .. }"
	  (when (member token '("{ subproof" "- bullet" "+ bullet" "* bullet"
				"." ". proofstart"))
	    (forward-char 1) ; skip de "."
	    (equal (coq-smie-forward-token) "{ subproof"))))
     (:after
      (cond
       ;; Override the default indent step added because of their presence
       ;; in smie-closer-alist.
       ((member token '(":" ":=" ":= with" ":= def" "- bullet" "+ bullet" "* bullet"
			"by" "in tactic" "<:" "<+" ":= record"
			"with module" "as" ":= inductive" ":= module" )) 2)

       ((equal token "with match") 4)

       ((equal token "; tactic") ; "; tactic" maintenant!!
	(cond
	 ((smie-rule-parent-p "; tactic") (smie-rule-separator kind))
	 (t (smie-rule-parent 2))))

       ; "as" tactical is not idented correctly
       ((equal token "in let") (smie-rule-parent))))

     (:before
      (cond

       ((equal token "with module")
	(if (smie-rule-parent-p "with module")
	    (smie-rule-parent)
	  (smie-rule-parent 4)))

       ((member token '("in tactic" "as" "by"))
	(cond
	 ((smie-rule-parent-p "- bullet" "+ bullet" "* bullet"
			      "{ subproof" ". proofstart")
	  (smie-rule-parent 4))
	 ((smie-rule-parent-p "in tactic") (smie-rule-parent))
	 (t (smie-rule-parent 2))))

       ((equal token "as")
	(if (smie-rule-parent-p "in tactic") (smie-rule-parent) 2))

       ((equal token "as morphism") (smie-rule-parent 2))
       ((member token '("xxx provedby" "with signature"))
	(if (smie-rule-parent-p "xxx provedby" "with signature")
	    (smie-rule-parent)
	  (smie-rule-parent 4)))


       ((and (member token '("forall" "quantif exists"))
	     (smie-rule-parent-p "forall" "exists quantif"))
	(smie-rule-parent))

       ;; This rule allows "End Proof" to align with corresponding ".
       ;; proofstart" PARENT instead of ". proofstart" itself
       ;;  Typically:
       ;;    "Proof" ". proofstart"
       ;;    "Qed" <- parent is ". proofstart" above
       ;; Align with the real command start of the ". xxxstart"
       ((member token '(". proofstart" ". modulestart"))
	(save-excursion (coq-find-real-start)
			`(column . ,(current-column))))

       ((member token '(":= module" ":= inductive" ":= def"))
	(if (smie-rule-hanging-p)
	    (save-excursion (coq-find-real-start)
			    `(column . ,(current-column)))
	  (save-excursion (coq-find-real-start)
			  `(column . ,(+ 2 (current-column))))))

       ((equal token "|")
	(cond ((smie-rule-parent-p "with match")
	       (- (funcall smie-rules-function :after "with match") 2))
	      ((smie-rule-prev-p ":= inductive")
	       (- (funcall smie-rules-function :after ":= inductive") 2))
	       
	      (t (smie-rule-separator kind))))))))

;; No need of this hack anymore?
;;       ((and (equal token "Proof End")
;;             (smie-rule-parent-p "Module" "Section" "goalcmd"))
;;        ;; ¡¡Major gross hack!!
;;        ;; This typically happens when a Lemma had no "Proof" keyword.
;;        ;; We should ideally find some other way to handle it (e.g. matching Qed
;;        ;; not with Proof but with any of the keywords like Lemma that can
;;        ;; start a new proof), but we can workaround the problem here, because
;;        ;; SMIE happened to decide arbitrarily that Qed will stop before Module
;;        ;; when parsing backward.
;;        ;; FIXME: This is fundamentally very wrong, but it seems to work
;;        ;; OK in practice.
;;        (smie-rule-parent 2))




(provide 'coq-smie-lexer)
