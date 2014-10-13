;; isar-syntax.el Syntax expressions for Isabelle/Isar
;; Copyright (C) 1994-2004, 2009, 2010 LFCS Edinburgh.
;; License:   GPL (GNU GENERAL PUBLIC LICENSE)
;;
;; Authors:     David Aspinall <David.Aspinall@ed.ac.uk>
;;              Markus Wenzel
;;
;; isar-syntax.el,v 12.0 2011/10/13 10:54:50 da Exp
;;

(require 'cl)				; remove-if, remove-if-not

(require 'proof-syntax)
(require 'isar-keywords)		; NB: we want to load isar-keywords at runtime

;; ----- character syntax

(defconst isar-script-syntax-table-entries
  '(?\$ "."
    ?\/ "."
    ?\\ "\\"
    ?+  "."
    ?-  "."
    ?=  "."
    ?%  "."
    ?<  "w"
    ?>  "w"
    ?\& "."
    ?.  "w"
    ?_  "w"
    ?\' "w"
    ??  "w"
    ?`  "\""
    ?\( "()1"
    ?\) ")(4"
    ?\{ "(}1b"
    ?\} "){4b"
    ?\* ". 23n")
   "Syntax table entries for Isar scripts.
This list is in the right format for proof-easy-config.")

(defconst isar-script-syntax-table-alist
  ;; NB: this is used for imenu.  Probably only need word syntax
  (let ((syn isar-script-syntax-table-entries)
	al)
    (while syn
      (setq al (cons (cons (char-to-string (car syn)) (cadr syn)) al))
      (setq syn (cddr syn)))
    al))

(defun isar-init-syntax-table ()
  "Set appropriate values for syntax table in current buffer."
  (let ((syn isar-script-syntax-table-entries))
    (while syn
      (modify-syntax-entry
       (car syn) (cadr syn))
      (setq syn (cddr syn)))))

(defun isar-init-output-syntax-table ()
  "Set appropriate values for syntax table for Isabelle output."
  (isar-init-syntax-table)
  ;; ignore strings so font-locking works inside them
  (modify-syntax-entry ?\" " ")
  (modify-syntax-entry ?`  " ")
  (modify-syntax-entry ?\* ".")
  (modify-syntax-entry ?\( "()")
  (modify-syntax-entry ?\) ")(")
  (modify-syntax-entry ?\{ "(}")
  (modify-syntax-entry ?\} "){"))


;; ----- keyword groups

(defconst isar-keyword-begin "begin")
(defconst isar-keyword-end "end")

(defconst isar-keywords-theory-enclose
  (append isar-keywords-theory-begin
	  isar-keywords-theory-switch
	  isar-keywords-theory-end))

(defconst isar-keywords-theory
  (append isar-keywords-theory-heading
	  isar-keywords-theory-decl
	  isar-keywords-theory-goal))

(defconst isar-keywords-save
  (append isar-keywords-qed
	  isar-keywords-qed-block
	  isar-keywords-qed-global))

(defconst isar-keywords-proof-enclose
  (append isar-keywords-proof-block
	  isar-keywords-proof-open
	  isar-keywords-proof-close
	  isar-keywords-qed-block))

(defconst isar-keywords-proof
  (append isar-keywords-proof-heading
	  isar-keywords-proof-goal
	  isar-keywords-proof-chain
	  isar-keywords-proof-decl
	  isar-keywords-qed))

(defconst isar-keywords-proof-context
  (append isar-keywords-proof-asm
	  isar-keywords-proof-asm-goal))

(defconst isar-keywords-local-goal
  (append isar-keywords-proof-goal
	  isar-keywords-proof-asm-goal))

(defconst isar-keywords-proper
  (append isar-keywords-theory
	  isar-keywords-proof-enclose
	  isar-keywords-proof))

(defconst isar-keywords-improper
  (append isar-keywords-theory-script
	  isar-keywords-proof-script
	  isar-keywords-qed-global))

(defconst isar-keyword-level-alist
  (append 
   (mapcar (lambda (w) (cons w 1))
	   (append isar-keywords-theory-heading
		   isar-keywords-theory-begin
		   isar-keywords-theory-end))
   (mapcar (lambda (w) (cons w 2))
	   (append isar-keywords-theory-script
		   isar-keywords-theory-goal))
   (mapcar (lambda (w) (cons w 3))
	   (append isar-keywords-proof-heading
		   isar-keywords-theory-goal))
   (mapcar (lambda (w) (cons w 4))
	   isar-keywords-proof-block)))

(defconst isar-keywords-outline 
  (mapcar 'car isar-keyword-level-alist))

(defconst isar-keywords-indent-open
  (append isar-keywords-theory-goal
	  isar-keywords-proof-goal
	  isar-keywords-proof-asm-goal
	  isar-keywords-proof-open
          '("notepad")))

(defconst isar-keywords-indent-close
  (append isar-keywords-save
	  isar-keywords-proof-close
          isar-keywords-theory-end))

(defconst isar-keywords-indent-enclose
  (append isar-keywords-proof-block
	  isar-keywords-proof-close
	  isar-keywords-qed-block
          isar-keywords-theory-end
	  (list isar-keyword-begin)))


;; ----- regular expressions

(defconst isar-ext-first "\\(?:\\\\<\\^?[A-Za-z]+>\\|[A-Za-z]\\)")
(defconst isar-ext-rest "\\(?:\\\\<\\^?[A-Za-z]+>\\|[A-Za-z0-9'_]\\)")

(defconst isar-text "[^\^A- ]*")
(defconst isar-long-id-stuff (concat "\\(?:" isar-ext-rest "\\|\\.\\)+"))
(defconst isar-id (concat "\\(" isar-ext-first isar-ext-rest "*\\)"))
(defconst isar-idx (concat isar-id "\\(?:\\.[0-9]+\\)?"))

(defconst isar-string "\"\\(\\(?:[^\"]\\|\\\\\"\\)*\\)\"")

(defun isar-ids-to-regexp (ids)
  "Hack list IDS of keywords IDS to make a regexp matching any of them.
Note: IDS may have full-stops already regexp quoted." ; a nuisance!
  (let* ((unquoted     (mapcar (lambda (s)
			 (replace-regexp-in-string (regexp-quote "\\.") "." s))
			       ids))
	 (cleaned      (remove "{" (remove "}" unquoted)))
	 (words	       (if cleaned (list (regexp-opt cleaned 'words))))
	 ;; } is not a word constituent, so \_<}\_> fails
	 (rbrace       (if (member "}" ids) '("}")))
	 ;; { similarly, must also prevent {* matching
	 (lbrace       (if (member "{" ids)
			   '("\\(?:{\\(?:\\b\\|[^\\*]\\)\\)"))))
    (mapconcat 'identity (append words lbrace rbrace) "\\|")))

;; tests
; (isar-ids-to-regexp '("bla" "blubber"))
; (isar-ids-to-regexp '("bla" "\\." "blubber"))
; (isar-ids-to-regexp '("bla" "\\." "blubber" "{"))
; NB: string-match not entirely accurate, syntax table affects \_< \_> behaviour
; (string-match (isar-ids-to-regexp '("bla" "}" "blubber" "{")) "}")  ; 0
; (string-match (isar-ids-to-regexp '("bla" "}" "blubber" "{")) "*}") ; 1 [OK]
; (string-match (isar-ids-to-regexp '("bla" "}" "blubber" "{")) "*}bla") ; 1 [OK]
; (string-match (isar-ids-to-regexp '("bla" "}" "blubber" "{")) "ug{*") ; nil
; (string-match (isar-ids-to-regexp '("bla" "}" "blubber" "{")) "ug{") ; 2
; (string-match (isar-ids-to-regexp '("bla" "}" "blubber" "{")) "}ug") ; 0
; (string-match (isar-ids-to-regexp '("bla" "}" "blubber" "{")) "}\n ug") ; 0
; (string-match (isar-ids-to-regexp '("foo" "\\." "Foo\\.bar")) "boo.foo") ; nil/4
; (string-match (isar-ids-to-regexp '("foo" "\\." "Foo\\.bar")) "Foo.bar") ; 0
; (string-match (isar-ids-to-regexp '("foo" "\\." "Foo\\.bar")) "bar.foo") ; 4
; (string-match (isar-ids-to-regexp '("foo" "\\." "Foo\\.bar")) "bar. foo") ; 5

(defconst isar-any-command-regexp
  ;; allow terminator to be considered as command start: 
  ;; FIXME: really needs change in generic function to take account of this,
  ;; since the end character of a command is not the start 
  (concat ";\\|" (isar-ids-to-regexp isar-keywords-major))
  "Regexp matching any Isabelle/Isar command keyword or the terminator character.")

(defconst isar-name-regexp
  (concat "\\s-*\\(" isar-string "\\|" isar-id "\\)\\s-*")
  "Regexp matching Isabelle/Isar names; surrounding space and contents grouped.
Group number 1 matches the identifier possibly with quotes; group number 2
matches contents of quotes for quoted identifiers.")

(defconst isar-improper-regexp
  "\\(\\<[A-Za-z][A-Za-z0-9'_]*_tac\\>\\|\\<goal[0-9]+\\>\\)"
  "Regexp matching low-level features")

(defconst isar-save-command-regexp
  (proof-anchor-regexp (isar-ids-to-regexp isar-keywords-save)))

(defconst isar-global-save-command-regexp
  (proof-anchor-regexp (isar-ids-to-regexp isar-keywords-qed-global)))

(defconst isar-goal-command-regexp
  (proof-anchor-regexp (isar-ids-to-regexp isar-keywords-theory-goal)))

(defconst isar-local-goal-command-regexp
  (proof-anchor-regexp (isar-ids-to-regexp isar-keywords-local-goal)))

(defconst isar-comment-start "(*")
(defconst isar-comment-end "*)")
(defconst isar-comment-start-regexp (regexp-quote isar-comment-start))
(defconst isar-comment-end-regexp (regexp-quote isar-comment-end))

(defconst isar-string-start-regexp "\"\\|`\\|{\\*")
(defconst isar-string-end-regexp "\"\\|`\\|\\*}")

(defun isar-syntactic-context ()
  (let ((sc (proof-looking-at-syntactic-context-default)))
    (or (if (eq sc 'string)
	    (save-excursion
	      (save-match-data
		(and (or (looking-at isar-string-start-regexp)
			 (re-search-backward isar-string-start-regexp nil t))
		     (skip-chars-backward " \t\n-")
		     (looking-at "[ \t\n]*--")
		     'comment))))
      sc)))


;; antiquotations

(defconst isar-antiq-regexp
  (concat "@{\\(?:[^\"{}]\\|" isar-string "\\)*}")
  "Regexp matching Isabelle/Isar antiquotations.")

;; keyword nesting

(defconst isar-nesting-regexp
  (isar-ids-to-regexp (list isar-keyword-begin isar-keyword-end)))

(defun isar-nesting ()
  "Determine keyword nesting"
  (let ((nesting 0) (limit (point)))
    (save-excursion
      (goto-char (point-min))
      (while (proof-re-search-forward isar-nesting-regexp limit t)
	(cond
	 ((proof-buffer-syntactic-context))
	 ((equal (match-string 0) isar-keyword-begin) (incf nesting))
	 ((equal (match-string 0) isar-keyword-end) (decf nesting)))))
    nesting))

(defun isar-match-nesting (limit)
  (block nil
    (while (proof-re-search-forward isar-nesting-regexp limit t)
      (and (not (proof-buffer-syntactic-context))
	   (if (equal (match-string 0) isar-keyword-begin)
	       (> (isar-nesting) 1)
	     (> (isar-nesting) 0))
	   (return t)))))


;; ----- Isabelle inner syntax highlight

(defface isabelle-string-face 
  (proof-face-specs
   (:foreground "springgreen4")
   (:background "springgreen1")
   ())
  "*Face for fontifying string contents in Isabelle."
  :group 'proof-faces)

(defface isabelle-quote-face 
  (proof-face-specs
   (:foreground "Gray80")
   (:background "Gray30")
   (:italic t))
  "*Face for quotes (string delimiters) in Isabelle."
  :group 'proof-faces)

(defface isabelle-class-name-face
  (proof-face-specs
   (:foreground "red")
   (:foreground "red3")
   (:bold t))
  "*Face for Isabelle term / type highlighting"
  :group 'proof-faces)

(defface isabelle-tfree-name-face
  (proof-face-specs
   (:foreground "purple")
   (:foreground "purple3")
   (:bold t))
  "*Face for Isabelle term / type highlighting"
  :group 'proof-faces)

(defface isabelle-tvar-name-face
  (proof-face-specs
   (:foreground "purple")
   (:foreground "purple3")
   (:bold t))
  "*Face for Isabelle term / type highlighting"
  :group 'proof-faces)

(defface isabelle-free-name-face
  (proof-face-specs
   (:foreground "blue")
   (:foreground "blue3")
   (:bold t))
  "*Face for Isabelle term / type highlighting"
  :group 'proof-faces)

(defface isabelle-bound-name-face
  (proof-face-specs
   (:foreground "green4")
   (:foreground "green")
   (:bold t))
  "*Face for Isabelle term / type highlighting"
  :group 'proof-faces)

(defface isabelle-var-name-face
  (proof-face-specs
   (:foreground "darkblue")
   (:foreground "blue3")
   (:bold t))
  "*Face for Isabelle term / type highlighting"
  :group 'proof-faces)

(defconst isabelle-string-face 'isabelle-string-face)
(defconst isabelle-quote-face  'isabelle-quote-face)
(defconst isabelle-class-name-face 'isabelle-class-name-face)
(defconst isabelle-tfree-name-face 'isabelle-tfree-name-face)
(defconst isabelle-tvar-name-face  'isabelle-tvar-name-face)
(defconst isabelle-free-name-face  'isabelle-free-name-face)
(defconst isabelle-bound-name-face 'isabelle-bound-name-face)
(defconst isabelle-var-name-face   'isabelle-var-name-face)


;; font-lock syntactic fontification

;; adapted from font-lock.el in GNU Emacs 23.1.1
(defun isar-font-lock-fontify-syntactically-region 
  (start end &optional loudly ppss)
  "Put proper face on each string and comment between START and END.
START should be at the beginning of a line."
  (let ((comment-end-regexp
	 (replace-regexp-in-string "^ *" "" comment-end))
        state beg)
    (if loudly (message "Fontifying %s... (syntactically...)" (buffer-name)))
    (goto-char start)
    ;;
    ;; Find the `start' state.
    (setq state (or ppss (syntax-ppss start)))
    ;;
    ;; Find each interesting place between here and `end'.
    (while
	(let ((instring     (nth 3 state))
	      (incomment    (nth 4 state)))
	  (when (or instring incomment)
	    (setq beg (max (nth 8 state) start))
	    (setq state (parse-partial-sexp (point) end nil nil state
					    'syntax-table))
	    (cond
	     (instring
	      (put-text-property (1+ beg)
				 (1- (point)) 'face isabelle-string-face)
	      (put-text-property beg (1+ beg) 'face isabelle-quote-face)
	      (put-text-property (1- (point)) (point) 'face isabelle-quote-face))
	     (t
	      (put-text-property beg (point) 'face font-lock-comment-face))))
	  (< (point) end))
      (setq state (parse-partial-sexp (point) end nil nil state
				      'syntax-table)))))

;; font-lock keywords fontification

(defvar isar-font-lock-keywords-1
  (list
   (cons 'isar-match-nesting                               'font-lock-preprocessor-face)
   (cons (isar-ids-to-regexp isar-keywords-minor)          'font-lock-type-face)
   (cons (isar-ids-to-regexp isar-keywords-control)        'proof-error-face)
   (cons (isar-ids-to-regexp isar-keywords-diag)           'proof-tacticals-name-face)
   (cons (isar-ids-to-regexp isar-keywords-theory-enclose) 'font-lock-type-face)
   (cons (isar-ids-to-regexp isar-keywords-proper)         'font-lock-keyword-face)
   (cons (isar-ids-to-regexp isar-keywords-proof-context)  'proof-declaration-name-face)
   (cons (isar-ids-to-regexp isar-keywords-improper)       'font-lock-reference-face)
   (cons isar-improper-regexp 'font-lock-reference-face)
   (cons isar-antiq-regexp '(0 'font-lock-variable-name-face t))))

(put 'isar-goals-mode
     'font-lock-extra-managed-props '(invisible sendback))
(put 'isar-response-mode
     'font-lock-extra-managed-props '(invisible sendback))

(defun isar-output-flkprops (start regexp end props)
  `(,(concat "\\(" start "\\)\\(" regexp "\\)\\(" end "\\)")
    (1 '(face nil invisible t) prepend)
    (2 ',props prepend)
    (,(+ 3 (regexp-opt-depth regexp)) '(face nil invisible t) prepend)))

(defun isar-output-flk (start regexp end face)
  (isar-output-flkprops start regexp end (list 'face face)))

(defvar isar-output-font-lock-keywords-1
  (list
   '("\^A[IJKLMNOPV]" (0 '(face nil invisible t) t))
   (isar-output-flkprops
    "\^AW" "\\(?:[^\^A]\\|\^A[^X]\\)*" "\^AX"
    '(face (:underline t) mouse-face 'highlight sendback t))

   (isar-output-flk "\^A0"
		    "\\(?:[^\^A]\\|\^A[^1]\\)*" "\^A1"
		    'proof-warning-face)

;; done generically at the moment:
;; (isar-output-flk "\^AM" "\\(?:[^\^A]\\|\^A[^N]\\)*" "\^AN" 'proof-error-face)

   (isar-output-flk "\^AB" isar-text "\^AA" 'isabelle-class-name-face)
   (isar-output-flk "\^AC" isar-text "\^AA" 'isabelle-tfree-name-face)
   (isar-output-flk "\^AD" isar-text "\^AA" 'isabelle-tvar-name-face)
   (isar-output-flk "\^AE" isar-text "\^AA" 'isabelle-free-name-face)
   (isar-output-flk "\^AF" isar-text "\^AA" 'isabelle-bound-name-face)
   (isar-output-flk "\^AG" isar-text "\^AA" 'isabelle-var-name-face)
   (isar-output-flk "\^AH" isar-text "\^AA" 'proof-declaration-name-face)
   )
  "*Font-lock table for Isabelle output terms.")

(defun isar-strip-output-markup (string)
  "Remove invisible output markup from STRING"
  (replace-regexp-in-string "\^A." "" string))

(defconst isar-shell-font-lock-keywords
  '(("\^A." (0 '(face nil invisible t)))))

(defvar isar-goals-font-lock-keywords
  (append
   (list
    "^theory:"
    "^proof (prove):"
    "^proof (state):"
    "^proof (chain):"
    "^goal.*:"
    "^picking.*:"
    "^using.*:"
    "^calculation:"
    "^this:"
    "^abbreviations:"
    "^term bindings:"
    "^facts:"
    "^cases:"
    "^prems:"
    "^fixed variables:"
    "^structures:"
    "^abbreviations:"
    "^type constraints:"
    "^default sorts:"
    "^used type variable names:"
    "^flex-flex pairs:"
    "^constants:"
    "^variables:"
    "^type variables:"
    "^\\s-*[0-9][0-9]?\\. ")
   isar-output-font-lock-keywords-1)
  "*Font-lock table for Isabelle/Isar output.")


;; ----- variations on undo

(defconst isar-linear-undo "linear_undo")

(defconst isar-undo "ProofGeneral.undo;")

(defconst isar-pr
  (if (member "ProofGeneral\\.pr" 
	      isar-keywords-major)
      "ProofGeneral.pr" ; does right thing
    "pr" ; See Trac #292 
    ))

(defun isar-remove (name)
  (concat "init_toplevel; kill_thy " name ";"))

(defun isar-undos (linearp i)
  (if (> i 0) (concat (if linearp "linear_undo " "undos_proof ")
		      (int-to-string i) ";"
		      (if linearp 
			  (concat " "
				  isar-pr
				  ";"))
		      )
    nil))  ; was proof-no-command

(defun isar-cannot-undo (cmd)
  (concat "cannot_undo \"" cmd "\";"))

(defconst isar-undo-commands
  (list
   isar-linear-undo
   isar-undo
   "init_toplevel" "kill_thy"
   "undos_proof"
   "cannot_undo"))

(defconst isar-theory-start-regexp
  (proof-anchor-regexp
   (isar-ids-to-regexp
    (append isar-keywords-theory-begin
	    isar-keywords-theory-switch))))

(defconst isar-end-regexp
  (proof-anchor-regexp
   (isar-ids-to-regexp isar-keywords-theory-end)))

(defconst isar-undo-fail-regexp
  (proof-anchor-regexp
   (isar-ids-to-regexp isar-keywords-control)))

(defconst isar-undo-skip-regexp
  (proof-anchor-regexp (proof-regexp-alt (isar-ids-to-regexp isar-keywords-diag) ";")))

(defconst isar-undo-ignore-regexp
  (proof-anchor-regexp "--"))

(defconst isar-undo-remove-regexp
  (concat
   (proof-anchor-regexp (isar-ids-to-regexp isar-keywords-theory-begin))
   isar-name-regexp))


;; ----- imenu

(defconst isar-keywords-imenu
  (append isar-keywords-theory-begin
	  isar-keywords-theory-heading
	  isar-keywords-theory-decl
	  isar-keywords-theory-script
	  isar-keywords-theory-goal))

(defconst isar-entity-regexp 
  (concat "\\(" (isar-ids-to-regexp isar-keywords-imenu) "\\)"))

(defconst isar-named-entity-regexp
  (concat isar-entity-regexp
	  "\\(?:\\s-*(\\s-*in[^)]+)\\)?"
	  isar-name-regexp "[[:=]" ))

(defconst isar-named-entity-name-match-number
          (1+ (regexp-opt-depth isar-entity-regexp)))

(defconst isar-generic-expression
  (mapcar (lambda (kw)
	    (list (capitalize kw)
		  (concat "\\<" kw "\\>"
			  "\\(?:\\s-*(\\s-*in[^)]+)\\)?"
			  isar-name-regexp "[[:=]")
		  1))
	  isar-keywords-imenu))

;; ----- indentation

(defconst isar-indent-any-regexp
  (proof-regexp-alt isar-any-command-regexp "\\s(" "\\s)"))
(defconst isar-indent-inner-regexp
  (proof-regexp-alt "[[]()]"))
(defconst isar-indent-enclose-regexp
  (proof-regexp-alt (isar-ids-to-regexp isar-keywords-indent-enclose) "\\s)"))
(defconst isar-indent-open-regexp
  (proof-regexp-alt (isar-ids-to-regexp isar-keywords-indent-open) "\\s("))
(defconst isar-indent-close-regexp
  (proof-regexp-alt (isar-ids-to-regexp isar-keywords-indent-close) "\\s)"))


;; ----- outline mode

(defconst isar-outline-regexp
  (concat "[ \t]*\\(?:" (isar-ids-to-regexp isar-keywords-outline) "\\)")
  "Outline regexp for Isabelle/Isar documents")

(defconst isar-outline-heading-end-regexp "\n")

(defconst isar-outline-heading-alist isar-keyword-level-alist)


(provide 'isar-syntax)
