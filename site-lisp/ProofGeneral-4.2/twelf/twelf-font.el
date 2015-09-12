;; twelf-font.el  Font lock configuration for Twelf
;;
;; Author: Frank Pfenning
;;	   Taken from Twelf's emacs mode and
;;	   adapted for Proof General by David Aspinall <David.Aspinall@ed.ac.uk>
;;
;; twelf-font.el,v 12.0 2011/10/13 10:54:51 da Exp
;;
;;

(require 'font-lock)

;; FIXME da: integrate with PG's face mechanism?
;; (but maybe keep twelf faces to help users)
;; Also should add font locking.

;; FIXME da: the twelf faces don't work with PG's
;; background colouring, why?


;; modify the syntax table so _ and ' are word constituents
;; otherwise the regexp's for identifiers become very complicated
;; FIXME: fn undef'd(set-word ?\_)
;; FIXME: fn (set-word ?\')

;; setting faces here...
;; use devices to improve portability?
;; make it dependent on light background vs dark background
;; tie in X resources?

(defun twelf-font-create-face (face from-face color)
  "Creates a Twelf font from FROM-FACE with COLOR."
  (make-face face)
  ;(reset-face face)			; seems to be necessary, but why?
  (copy-face from-face face)
  (if color (set-face-foreground face color)))

(defvar twelf-font-dark-background nil
  "*T if the background of Emacs is to be considered dark.")

;; currently we not using bold or italics---some font families
;; work poorly with that kind of face.
(cond (twelf-font-dark-background
       (twelf-font-create-face 'twelf-font-keyword-face 'default nil)
       (twelf-font-create-face 'twelf-font-comment-face 'font-lock-comment-face
			     nil)
       (twelf-font-create-face 'twelf-font-percent-key-face 'default "Plum")
       (twelf-font-create-face 'twelf-font-decl-face 'default "Orange")
       (twelf-font-create-face 'twelf-font-parm-face 'default "Orange")
       (twelf-font-create-face 'twelf-font-fvar-face 'default "SpringGreen")
       (twelf-font-create-face 'twelf-font-evar-face 'default "Aquamarine"))
      (t
       (twelf-font-create-face 'twelf-font-keyword-face 'default nil)
       (twelf-font-create-face 'twelf-font-comment-face 'font-lock-comment-face
			     nil)
       (twelf-font-create-face 'twelf-font-percent-key-face 'default "MediumPurple")
       (twelf-font-create-face 'twelf-font-decl-face 'default "FireBrick")
       (twelf-font-create-face 'twelf-font-parm-face 'default "Green4")
       (twelf-font-create-face 'twelf-font-fvar-face 'default "Blue1")
       (twelf-font-create-face 'twelf-font-evar-face 'default "Blue4")))

;; Note that the order matters!

(defvar twelf-font-patterns
 '(
   ;; delimited comments, perhaps should use different font
   ;;("%{" "}%" comment)
   (twelf-font-find-delimited-comment . twelf-font-comment-face)
   ;; single-line comments
   ;; replace \\W by \\s- for whitespace?
   ("%\\W.*$" 0 twelf-font-comment-face)
   ;; %keyword declarations
   ("\\(%infix\\|%prefix\\|%prefix\\|%postfix\\|%name\\|%solve\\|%query\\|%mode\\|%terminates\\|%theorem\\|%prove\\).*$"
    1 twelf-font-percent-key-face nil)
   ;; keywords, omit punctuations for now.
   ("\\(\\<<-\\>\\|\\<->\\>\\|\\<type\\>\\|\\<=\\>\\|\\<_\\>\\)"
    ;; for LLF, no punctuation marks
;;"\\(\\<<-\\>\\|\\<->\\>\\|\\<o-\\>\\|\\<-o\\>\\|\\<<T>\\>\\|\\<&\\>\\|\\^\\|()\\|\\<type\\>\\|\\<sigma\\>\\)"
    ;; for LLF, with punctuation marks
    ;;"\\([][:.(){},]\\|\\<<-\\>\\|\\<->\\>\\|\\<o-\\>\\|\\<-o\\>\\|\\<<T>\\>\\|\\<&\\>\\|\\^\\|()\\|\\<type\\>\\|\\<sigma\\>\\)"
    ;; for Elf, no punction marks
    ;;"\\(\\<<-\\>\\|\\<->\\>\\|\\<type\\>\\|\\<sigma\\>\\)"
    ;; for Elf, including punctuation marks
    ;;"\\([][:.(){}]\\|\\<<-\\>\\|\\<->\\>\\|\\<type\\>\\|\\<sigma\\>\\)"
   . twelf-font-keyword-face)
   ;; declared constants
   (twelf-font-find-decl . twelf-font-decl-face)
   ;; parameters
   (twelf-font-find-parm . twelf-font-parm-face)
   ;; quantified existentials
   (twelf-font-find-evar . twelf-font-evar-face)
   ;; lower-case identifiers (almost = constants)
   ;;("\\<\\([a-z!&$^+/<=>?@~|#*`;,]\\|\\-\\|\\\\\\)\\w*\\>"
   ;; nil black)
   ;; upper-case identifiers (almost = variables)
   ("\\<[A-Z_]\\w*\\>" . twelf-font-fvar-face)
   ;; numbers and quoted identifiers omitted for now
   )
 "Highlighting patterns for Twelf mode.
This generally follows the syntax of the FONT-LOCK-KEYWORDS variable,
but allows an arbitrary function to be called instead of just
regular expressions."
 )

(defun twelf-font-fontify-decl  ()
  "Fontifies the current Twelf declaration."
  (interactive)
  (let* ((region (twelf-current-decl))
	 (start (nth 0 region))
	 (end (nth 1 region)))
    (save-excursion
      (font-lock-unfontify-region start end)
      (twelf-font-fontify-region start end))))

(defun twelf-font-fontify-buffer ()
  "Fontitifies the current buffer as Twelf code."
  (interactive)
  (save-excursion
    (font-lock-unfontify-region (point-min) (point-max)) ; t optional in XEmacs
    (twelf-font-fontify-region (point-min) (point-max))))

(defun twelf-font-unfontify ()
  "Removes fontification from current buffer."
  (interactive)
  (font-lock-unfontify-region (point-min) (point-max)))	; t optional in XEmacs

(defvar font-lock-message-threshold 6000) ; in case we are running FSF Emacs

(defun twelf-font-fontify-region (start end)
  "Go through TWELF-FONT-PATTERNS, fontifying according to given functions"
  (save-restriction
    (narrow-to-region start end)
    (if (and font-lock-verbose
	     (>= (- end start) font-lock-message-threshold))
	(message "Fontifying %s... (semantically...)" (buffer-name)))
    (let ((patterns twelf-font-patterns)
	  (case-fold-search nil)	; in Twelf, never case-fold
	  (modified (buffer-modified-p)) ; for FSF Emacs 19
	  pattern
	  fun-or-regexp
	  instructions
	  face
	  match-index
	  allow-overlap-p
	  region)
      (while patterns
	(setq pattern (car patterns))
	(setq patterns (cdr patterns))
	(goto-char start)
	(cond ((stringp pattern)
	       (setq match-index 0)
	       (setq face 'font-lock-keyword-face)
	       (setq allow-overlap-p nil))
	      ((listp pattern)
	       (setq fun-or-regexp (car pattern))
	       (setq instructions (cdr pattern))
	       (cond ((integerp instructions)
		      (setq match-index instructions)
		      (setq face 'font-lock-keyword-face)
		      (setq allow-overlap-p nil))
		     ((symbolp instructions)
		      (setq match-index 0)
		      (setq face instructions)
		      (setq allow-overlap-p nil))
		     ((listp instructions)
		      (setq match-index (nth 0 instructions))
		      (setq face (nth 1 instructions))
		      (setq allow-overlap-p (nth 2 instructions)))
		     (t (error "Illegal font-lock-keyword instructions"))))
	      (t (error "Illegal font-lock-keyword instructions")))
	(cond ((symbolp fun-or-regexp)	; a function to call
	       (while
		   (setq region (funcall fun-or-regexp end))
		 ;; END is limit of forward search, start at point
		 ;; and move point
		 ;; check whether overlap is permissible!
		 (twelf-font-highlight (car region) (cdr region)
				     face allow-overlap-p)))
	      ((stringp fun-or-regexp)	; a pattern to find
	       (while
		   (re-search-forward fun-or-regexp end t)
		 (goto-char (match-end match-index)) ; back-to-back font hack
		 (twelf-font-highlight (match-beginning match-index)
				     (match-end match-index)
				     face
				     allow-overlap-p)))
	      (t (error "Illegal font-lock-keyword instructions"))))
      ;; For FSF Emacs 19: mark buffer not modified, if it wasn't before
      ;; fontification.
      (and (not modified) (buffer-modified-p) (set-buffer-modified-p nil))
      (if (and font-lock-verbose
	       (>= (- end start) font-lock-message-threshold))
	  (message "Fontifying %s... done" (buffer-name))))))

(defun twelf-font-highlight (start end face allow-overlap-p)
  "Highlight region between START and END with FONT.
If already highlighted and ALLOW-OVERLAP-P is nil, don't highlight."
  (or (= start end)
      ;;(if allow-overlap-p nil (font-lock-any-faces-p start (1- end)))
      ;; different in XEmacs 19.16?  font-lock-any-faces-p subtracts 1.
      (if allow-overlap-p nil (font-lock-any-faces-p start end))
      (font-lock-set-face start end face)))

(defun twelf-font-find-delimited-comment (limit)
  "Find a delimited Twelf comment and return (START . END), nil if none."
  (let ((comment-level nil)
	(comment-start nil))
    (if (search-forward "%{" limit t)
	(progn
	  (setq comment-start (- (point) 2))
	  (setq comment-level 1)
	  (while (and (> comment-level 0)
		      (re-search-forward "\\(%{\\)\\|\\(}%\\)"
					 limit 'limit))
	    (cond
	     ((match-beginning 1) (setq comment-level (1+ comment-level)))
	     ((match-beginning 2) (setq comment-level (1- comment-level)))))
	  (cons comment-start (point)))
      nil)))

;; doesn't work yet with LIMIT!!!
;; this should never be done in incremental-highlighting mode
(defun twelf-font-find-decl (limit)
  "Find an Twelf constant declaration and return (START . END), nil if none."
  (let (start
	end
	;; Turn off error messages
	(id (twelf-next-decl nil nil)))
    ;; ignore limit for now because of global buffer restriction
    (if (null id) ; (or (null id) (> (point) limit))
	nil
      (skip-chars-backward *whitespace*)
      (setq end (point))
      (beginning-of-line 1)
      (setq start (point))
      (twelf-end-of-par)
      (cons start end))))

(defun twelf-font-find-binder (var-pattern limit occ-face)
  "Find Twelf binder whose bound variable matches var-pattern.
Returns (START . END) if found, NIL if there is none before LIMIT.
Binders have the form [x],[x:A],{y},{y:A}.
As a side-effect, it highlights all occurrences of the bound
variable using the variable OCC-FACE."
  (let (start
	end
	par-end
	scope-start
	scope-end
	word
	(found nil))
    ;;; At the moment, ignore limit since restriction is done globally
    ;; (save-restriction
    ;; (narrow-to-region (point) limit)
      (while (not found)
	(skip-chars-forward "^[{%")
	(while (looking-at *twelf-comment-start*)
	  (cond ((looking-at "%{")
		 (condition-case nil (forward-sexp 1)
		   (error (goto-char (point-max))))
		 (or (eobp) (forward-char 1)))
		(t
		 (end-of-line 1)))
	  (skip-chars-forward "^[{%"))
	(if (eobp)
	    (setq found 'eob)
	  (forward-char 1)
	  (skip-chars-forward *whitespace*)
	  (if (looking-at var-pattern)
	      ;;"\\<\\w+\\>"
	      ;;"\\<[-a-z!&$^+/\\<=>?@~|#*`;,]\\w*\\>"
	      (setq found t))))
      (if (eq found 'eob)
	  nil
	(setq start (match-beginning 0))
	(setq end (match-end 0))
	(setq word (buffer-substring start end))
	;; find scope of quantifier
	(twelf-end-of-par)
	(setq par-end (point))
	(goto-char end)
	(condition-case nil (up-list 1)	; end of quantifier
	  (error (goto-char par-end)))
	(setq scope-start (min (point) par-end))
	(condition-case nil (up-list 1)	; end of scope
	  (error (goto-char par-end)))
	(setq scope-end (min (point) par-end))
	(goto-char scope-start)
	(while
	    ;; speed here???
	    (search-forward-regexp (concat "\\<" (regexp-quote word) "\\>")
				   scope-end 'limit)
	  ;; Check overlap here!!! --- current bug if in comment
	  (font-lock-set-face (match-beginning 0) (match-end 0)
			      occ-face))
	(goto-char end)
	(cons start end)))
  ;;)
  )

(defun twelf-font-find-parm (limit)
  "Find bound Twelf parameters and return (START . END), NIL if none.
Also highlights all occurrences of the parameter.
For these purposes, a parameter is a bound, lower-case identifier."
  (twelf-font-find-binder "\\<[-a-z!&$^+/\\<=>?@~|#*`;,]\\w*\\>"
			limit 'twelf-font-parm-face))

(defun twelf-font-find-evar (limit)
  "Find bound Twelf existential variable return (START . END), NIL if none.
Also highlights all occurrences of the existential variable.
For these purposes, an existential variable is a bound, upper-case identifier."
  (twelf-font-find-binder "\\<[A-Z_]\\w*\\>"
			limit 'twelf-font-evar-face))

; next two are now in twelf.el
;(define-key twelf-mode-map "\C-c\C-l" 'twelf-font-fontify-decl)
;(define-key twelf-mode-map "\C-cl" 'twelf-font-fontify-buffer)


;;;
;;;
;;; This comes from twelf-old.el but is needed for fontification,
;;;
;;; Perhaps some of these parsing functions will need reusing
;;; for sending input to server properly?
;;;

;;; FIXME: some of names need fixing for safe conventions.

(defun twelf-current-decl ()
  "Returns list (START END COMPLETE) for current Twelf declaration.
This should be the declaration or query under or just before
point within the nearest enclosing blank lines.
If declaration ends in `.' then COMPLETE is t, otherwise nil."
  (let (par-start par-end complete)
    (save-excursion
      ;; Skip backwards if between declarations
      (if (or (eobp) (looking-at (concat "[" *whitespace* "]")))
	  (skip-chars-backward (concat *whitespace* ".")))
      (setq par-end (point))
      ;; Move forward from beginning of decl until last
      ;; declaration before par-end is found.
      (if (not (bobp)) (backward-paragraph 1))
      (setq par-start (point))
      (while (and (twelf-end-of-par par-end)
		  (< (point) par-end))
	(setq par-start (point)))
      ;; Now par-start is at end of preceding declaration or query.
      (goto-char par-start)
      (skip-twelf-comments-and-whitespace)
      (setq par-start (point))
      ;; Skip to period or consective blank lines
      (setq complete (twelf-end-of-par))
      (setq par-end (point)))
    (list par-start par-end complete)))

(defun twelf-next-decl (filename error-buffer)
  "Set point after the identifier of the next declaration.
Return the declared identifier or `nil' if none was found.
FILENAME and ERROR-BUFFER are used if something appears wrong."
  (let ((id nil)
	end-of-id
	beg-of-id)
    (skip-twelf-comments-and-whitespace)
    (while (and (not id) (not (eobp)))
      (setq beg-of-id (point))
      (if (zerop (skip-chars-forward *twelf-id-chars*))
	  ;; Not looking at id: skip ahead
	  (skip-ahead filename (current-line-absolute) "No identifier"
		      error-buffer)
	(setq end-of-id (point))
	(skip-twelf-comments-and-whitespace)
	(if (not (looking-at ":"))
	    ;; Not looking at valid decl: skip ahead
	    (skip-ahead filename (current-line-absolute end-of-id) "No colon"
			error-buffer)
	  (goto-char end-of-id)
	  (setq id (buffer-substring beg-of-id end-of-id))))
      (skip-twelf-comments-and-whitespace))
    id))

(defconst *whitespace* " \t\n\f"
  "Whitespace characters to be skipped by various operations.")

(defconst *twelf-comment-start* (concat "%[%{" *whitespace* "]")
  "Regular expression to match the start of a Twelf comment.")

(defconst *twelf-id-chars* "a-z!&$^+/<=>?@~|#*`;,\\-\\\\A-Z_0-9'"
  "Characters that constitute Twelf identifiers.")

(defun skip-twelf-comments-and-whitespace ()
  "Skip Twelf comments (single-line or balanced delimited) and white space."
  (skip-chars-forward *whitespace*)
  (while (looking-at *twelf-comment-start*)
    (cond ((looking-at "%{")		; delimited comment
	   (condition-case nil (forward-sexp 1)
	     (error (goto-char (point-max))))
	   (or (eobp) (forward-char 1)))
	  (t				; single-line comment
	   (end-of-line 1)))
    (skip-chars-forward *whitespace*)))

(defun twelf-end-of-par (&optional limit)
  "Skip to presumed end of current Twelf declaration.
Moves to next period or blank line (whichever comes first)
and returns t if period is found, nil otherwise.
Skips over comments (single-line or balanced delimited).
Optional argument LIMIT specifies limit of search for period."
  (if (not limit)
      (save-excursion
	(forward-paragraph 1)
	(setq limit (point))))
  (while (and (not (looking-at "\\."))
	      (< (point) limit))
    (skip-chars-forward "^.%" limit)
    (cond ((looking-at *twelf-comment-start*)
	   (skip-twelf-comments-and-whitespace))
	  ((looking-at "%")
	   (forward-char 1))))
  (cond ((looking-at "\\.")
	 (forward-char 1)
	 t)
	(t ;; stopped at limit
	 nil)))

(defun skip-ahead (filename line message error-buffer)
  "Skip ahead when syntactic error was found.
A parsable error message constited from FILENAME, LINE, and MESSAGE is
deposited in ERROR-BUFFER."
  (if error-buffer
      (save-excursion
	(set-buffer error-buffer)
	(goto-char (point-max))
	(insert filename ":" (int-to-string line) " Warning: " message "\n")
	(setq *twelf-error-pos* (point))))
  (twelf-end-of-par))

(defun current-line-absolute (&optional char-pos)
  "Return line number of CHAR-POS (default: point) in current buffer.
Ignores any possible buffer restrictions."
  (1+ (count-lines 1 (or char-pos (point)))))


(provide 'twelf-font)
