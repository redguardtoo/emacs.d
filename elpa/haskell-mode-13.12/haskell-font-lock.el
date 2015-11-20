;;; haskell-font-lock.el --- Font locking module for Haskell Mode

;; Copyright 2003, 2004, 2005, 2006, 2007, 2008  Free Software Foundation, Inc.
;; Copyright 1997-1998  Graeme E Moss, and Tommy Thorn

;; Author: 1997-1998 Graeme E Moss <gem@cs.york.ac.uk>
;;         1997-1998 Tommy Thorn <thorn@irisa.fr>
;;         2003      Dave Love <fx@gnu.org>
;; Keywords: faces files Haskell

;; This file is not part of GNU Emacs.

;; This file is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 3, or (at your option)
;; any later version.

;; This file is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:

;; Purpose:
;;
;; To support fontification of standard Haskell keywords, symbols,
;; functions, etc.  Supports full Haskell 1.4 as well as LaTeX- and
;; Bird-style literate scripts.
;;
;; Installation:
;;
;; To turn font locking on for all Haskell buffers under the Haskell
;; mode of Moss&Thorn, add this to .emacs:
;;
;;    (add-hook 'haskell-mode-hook 'turn-on-haskell-font-lock)
;;
;; Otherwise, call `turn-on-haskell-font-lock'.
;;
;;
;; Customisation:
;;
;; The colours and level of font locking may be customised.  See the
;; documentation on `turn-on-haskell-font-lock' for more details.
;;
;; Present Limitations/Future Work (contributions are most welcome!):
;;
;; . Debatable whether `()' `[]' `(->)' `(,)' `(,,)' etc.  should be
;;   highlighted as constructors or not.  Should the `->' in
;;   `id :: a -> a' be considered a constructor or a keyword?  If so,
;;   how do we distinguish this from `\x -> x'?  What about the `\'?
;;
;; . XEmacs can support both `--' comments and `{- -}' comments
;;   simultaneously.  If XEmacs is detected, this should be used.
;;
;; . Support for GreenCard?
;;
;;
;; All functions/variables start with
;; `(turn-(on/off)-)haskell-font-lock' or `haskell-fl-'.

;;; Change Log:

;; Version 1.3:
;;   From Dave Love:
;;   Support for proper behaviour (including with Unicode identifiers)
;;   in Emacs 21 only hacked in messily to avoid disturbing the old
;;   stuff.  Needs integrating more cleanly.  Allow literate comment
;;   face to be customized.  Some support for fontifying definitions.
;;   (I'm not convinced the faces should be customizable -- fontlock
;;   faces are normally expected to be consistent.)
;;
;; Version 1.2:
;;   Added support for LaTeX-style literate scripts.  Allow whitespace
;;   after backslash to end a line for string continuations.
;;
;; Version 1.1:
;;   Use own syntax table.  Use backquote (neater).  Stop ''' being
;;   highlighted as quoted character.  Fixed `\"' fontification bug
;;   in comments.
;;
;; Version 1.0:
;;   Brought over from Haskell mode v1.1.

;;; Code:

(require 'cl-lib)
(require 'haskell-mode)
(require 'font-lock)

(defcustom haskell-font-lock-symbols nil
  "Display \\ and -> and such using symbols in fonts.
This may sound like a neat trick, but be extra careful: it changes the
alignment and can thus lead to nasty surprises w.r.t layout.
If t, try to use whichever font is available.  Otherwise you can
set it to a particular font of your preference among `japanese-jisx0208'
and `unicode'."
  :group 'haskell
  :type '(choice (const nil)
                 (const t)
                 (const unicode)
                 (const japanese-jisx0208)))

(defconst haskell-font-lock-symbols-alist
  (append
   ;; Prefer single-width Unicode font for lambda.
   (and (fboundp 'decode-char)
        (memq haskell-font-lock-symbols '(t unicode))
        (list (cons "\\" (decode-char 'ucs 955))))
   ;; The symbols can come from a JIS0208 font.
   (and (fboundp 'make-char) (fboundp 'charsetp) (charsetp 'japanese-jisx0208)
        (memq haskell-font-lock-symbols '(t japanese-jisx0208))
        (list (cons "not" (make-char 'japanese-jisx0208 34 76))
              (cons "\\" (make-char 'japanese-jisx0208 38 75))
              (cons "->" (make-char 'japanese-jisx0208 34 42))
              (cons "<-" (make-char 'japanese-jisx0208 34 43))
              (cons "=>" (make-char 'japanese-jisx0208 34 77))
              ;; FIXME: I'd like to either use ∀ or ∃ depending on how the
              ;; `forall' keyword is used, but currently the rest of the
              ;; code assumes that such ambiguity doesn't happen :-(
              (cons "forall" (make-char 'japanese-jisx0208 34 79))))
   ;; Or a unicode font.
   (and (fboundp 'decode-char)
        (memq haskell-font-lock-symbols '(t unicode))
        (list (cons "not" (decode-char 'ucs 172))
              (cons "->" (decode-char 'ucs 8594))
              (cons "<-" (decode-char 'ucs 8592))
              (cons "=>" (decode-char 'ucs 8658))
              (cons "()" (decode-char 'ucs #X2205))
              (cons "==" (decode-char 'ucs #X2261))
              (cons "/=" (decode-char 'ucs #X2262))
              (cons ">=" (decode-char 'ucs #X2265))
              (cons "<=" (decode-char 'ucs #X2264))
              (cons "!!" (decode-char 'ucs #X203C))
              (cons "&&" (decode-char 'ucs #X2227))
              (cons "||" (decode-char 'ucs #X2228))
              (cons "sqrt" (decode-char 'ucs #X221A))
              (cons "undefined" (decode-char 'ucs #X22A5))
              (cons "pi" (decode-char 'ucs #X3C0))
              (cons "~>" (decode-char 'ucs 8669)) ;; Omega language
              ;; (cons "~>" (decode-char 'ucs 8605)) ;; less desirable
              (cons "-<" (decode-char 'ucs 8610)) ;; Paterson's arrow syntax
              ;; (cons "-<" (decode-char 'ucs 10521)) ;; nicer but uncommon
              (cons "::" (decode-char 'ucs 8759))
              (list "." (decode-char 'ucs 8728) ; (decode-char 'ucs 9675)
                    ;; Need a predicate here to distinguish the . used by
                    ;; forall <foo> . <bar>.
                    'haskell-font-lock-dot-is-not-composition)
              (cons "forall" (decode-char 'ucs 8704)))))
  "Alist mapping Haskell symbols to chars.
Each element has the form (STRING . CHAR) or (STRING CHAR PREDICATE).
STRING is the Haskell symbol.
CHAR is the character with which to represent this symbol.
PREDICATE if present is a function of one argument (the start position
of the symbol) which should return non-nil if this mapping should be disabled
at that position.")

(defun haskell-font-lock-dot-is-not-composition (start)
  "Return non-nil if the \".\" at START is not a composition operator.
This is the case if the \".\" is part of a \"forall <tvar> . <type>\"."
  (save-excursion
    (goto-char start)
    (re-search-backward "\\<forall\\>[^.\"]*\\="
                        (line-beginning-position) t)))

(defface haskell-keyword-face
  '((t :inherit font-lock-keyword-face))
  "Face used to highlight Haskell keywords."
  :group 'haskell)

(defface haskell-constructor-face
  '((t :inherit font-lock-type-face))
  "Face used to highlight Haskell constructors."
  :group 'haskell)

;; This used to be `font-lock-variable-name-face' but it doesn't result in
;; a highlighting that's consistent with other modes (it's mostly used
;; for function defintions).
(defface haskell-definition-face
  '((t :inherit font-lock-function-name-face))
  "Face used to highlight Haskell definitions."
  :group 'haskell)

;; This is probably just wrong, but it used to use
;; `font-lock-function-name-face' with a result that was not consistent with
;; other major modes, so I just exchanged with `haskell-definition-face'.
(defface haskell-operator-face
  '((t :inherit font-lock-variable-name-face))
  "Face used to highlight Haskell operators."
  :group 'haskell)

(defface haskell-pragma-face
  '((t :inherit font-lock-comment-face))
  "Face used to highlight Haskell pragmas."
  :group 'haskell)

(defface haskell-default-face
  '((t :inherit default))
  "Face used to highlight ordinary Haskell code."
  :group 'haskell)

(defface haskell-literate-comment-face
  '((t :inherit font-lock-doc-face))
  "Face with which to fontify literate comments.
Inherit from `default' to avoid fontification of them."
  :group 'haskell)

;; These variables exist only for backward compatibility.
(defvar haskell-keyword-face 'haskell-keyword-face)
(defvar haskell-constructor-face 'haskell-constructor-face)
(defvar haskell-definition-face 'haskell-definition-face)
(defvar haskell-operator-face 'haskell-operator-face)
(defvar haskell-pragma-face 'haskell-pragma-face)
(defvar haskell-default-face 'haskell-default-face)
(defvar haskell-literate-comment-face 'haskell-literate-comment-face)

(defun haskell-font-lock-compose-symbol (alist)
  "Compose a sequence of ascii chars into a symbol.
Regexp match data 0 points to the chars."
  ;; Check that the chars should really be composed into a symbol.
  (let* ((start (match-beginning 0))
         (end (match-end 0))
         (syntaxes (cond
                    ((eq (char-syntax (char-after start)) ?w) '(?w))
                    ;; Special case for the . used for qualified names.
                    ((and (eq (char-after start) ?\.) (= end (1+ start)))
                     '(?_ ?\\ ?w))
                    (t '(?_ ?\\))))
         sym-data)
    (if (or (memq (char-syntax (or (char-before start) ?\ )) syntaxes)
            (memq (char-syntax (or (char-after end) ?\ )) syntaxes)
            (or (elt (syntax-ppss) 3) (elt (syntax-ppss) 4))
            (and (consp (setq sym-data (cdr (assoc (match-string 0) alist))))
                 (let ((pred (cadr sym-data)))
                   (setq sym-data (car sym-data))
                   (funcall pred start))))
        ;; No composition for you.  Let's actually remove any composition
        ;; we may have added earlier and which is now incorrect.
        (remove-text-properties start end '(composition))
      ;; That's a symbol alright, so add the composition.
      (compose-region start end sym-data)))
  ;; Return nil because we're not adding any face property.
  nil)

(defun haskell-font-lock-symbols-keywords ()
  (when (fboundp 'compose-region)
    (let ((alist nil))
      (dolist (x haskell-font-lock-symbols-alist)
        (when (and (if (fboundp 'char-displayable-p)
                       (char-displayable-p (if (consp (cdr x)) (cadr x) (cdr x)))
                     (if (fboundp 'latin1-char-displayable-p)
                         (latin1-char-displayable-p (if (consp (cdr x))
                                                        (cadr x)
                                                      (cdr x)))
                       t))
                   (not (assoc (car x) alist))) ; Not yet in alist.
          (push x alist)))
      (when alist
        `((,(regexp-opt (mapcar 'car alist) t)
           (0 (haskell-font-lock-compose-symbol ',alist)
              ;; In Emacs-21, if the `override' field is nil, the face
              ;; expressions is only evaluated if the text has currently
              ;; no face.  So force evaluation by using `keep'.
              keep)))))))

(defun haskell-font-lock-find-pragma (end)
  (catch 'haskell-font-lock-find-pragma
    (while (search-forward "{-#" end t)
      (let* ((begin (match-beginning 0))
             (ppss (save-excursion (syntax-ppss begin))))
        ;; We're interested only when it's not in a string or a comment.
        (unless (or (nth 3 ppss)
                    (nth 4 ppss))
          ;; Find the end of the pragma.
          (let ((end (scan-lists begin 1 0)))
            ;; Match data contains only the opening {-#, update it to cover the
            ;; whole pragma.
            (set-match-data (list begin end))
            ;; Move to the end so we don't start the next scan from inside the
            ;; pragma we just found.
            (goto-char end)
            (throw 'haskell-font-lock-find-pragma t)))))
    ;; Found no pragma.
    nil))

;; The font lock regular expressions.
(defun haskell-font-lock-keywords-create (literate)
  "Create fontification definitions for Haskell scripts.
Returns keywords suitable for `font-lock-keywords'."
  (let* (;; Bird-style literate scripts start a line of code with
         ;; "^>", otherwise a line of code starts with "^".
         (line-prefix (if (eq literate 'bird) "^> ?" "^"))

         ;; Most names are borrowed from the lexical syntax of the Haskell
         ;; report.
         ;; Some of these definitions have been superseded by using the
         ;; syntax table instead.

         ;; (ASCsymbol "-!#$%&*+./<=>?@\\\\^|~")
         ;; Put the minus first to make it work in ranges.

         ;; We allow _ as the first char to fit GHC
         (varid "\\b[[:lower:]_][[:alnum:]'_]*\\b")
         ;; We allow ' preceding conids because of DataKinds/PolyKinds
         (conid "\\b'?[[:upper:]][[:alnum:]'_]*\\b")
         (modid (concat "\\b" conid "\\(\\." conid "\\)*\\b"))
         (qvarid (concat modid "\\." varid))
         (qconid (concat modid "\\." conid))
         (sym
          ;; We used to use the below for non-Emacs21, but I think the
          ;; regexp based on syntax works for other emacsen as well.  -- Stef
          ;; (concat "[" symbol ":]+")
          ;; Add backslash to the symbol-syntax chars.  This seems to
          ;; be thrown for some reason by backslash's escape syntax.
          "\\(\\s_\\|\\\\\\)+")

         ;; Reserved operations
         (reservedsym
          (concat "\\S."
                  ;; (regexp-opt '(".." "::" "=" "\\" "|" "<-" "->"
                  ;;            "@" "~" "=>") t)
                  "\\(->\\|→\\|\\.\\.\\|::\\|∷\\|<-\\|←\\|=>\\|[=@\\|~]\\)"
                  "\\S."))
         ;; Reserved identifiers
         (reservedid
          (concat "\\<"
                  ;; `as', `hiding', and `qualified' are part of the import
                  ;; spec syntax, but they are not reserved.
                  ;; `_' can go in here since it has temporary word syntax.
                  ;; (regexp-opt
                  ;;  '("case" "class" "data" "default" "deriving" "do"
                  ;;    "else" "if" "import" "in" "infix" "infixl"
                  ;;    "infixr" "instance" "let" "module" "newtype" "of"
                  ;;    "then" "type" "where" "_") t)
                  "\\(_\\|c\\(ase\\|lass\\)\\|d\\(ata\\|e\\(fault\\|riving\\)\\|o\\)\\|else\\|i\\(mport\\|n\\(fix[lr]?\\|stance\\)\\|[fn]\\)\\|let\\|module\\|mdo\\|newtype\\|of\\|rec\\|proc\\|t\\(hen\\|ype\\)\\|where\\)"
                  "\\>"))

         ;; This unreadable regexp matches strings and character
         ;; constants.  We need to do this with one regexp to handle
         ;; stuff like '"':"'".  The regexp is the composition of
         ;; "([^"\\]|\\.)*" for strings and '([^\\]|\\.[^']*)' for
         ;; characters, allowing for string continuations.
         ;; Could probably be improved...
         (string-and-char
          (concat "\\(\\(\"\\|" line-prefix "[ \t]*\\\\\\)\\([^\"\\\\\n]\\|\\\\.\\)*\\(\"\\|\\\\[ \t]*$\\)\\|'\\([^'\\\\\n]\\|\\\\.[^'\n]*\\)'\\)"))

         ;; Top-level declarations
         (topdecl-var
          (concat line-prefix "\\(" varid "\\(?:\\s-*,\\s-*" varid "\\)*" "\\)\\s-*"
                  ;; optionally allow for a single newline after identifier
                  ;; NOTE: not supported for bird-style .lhs files
                  (if (eq literate 'bird) nil "\\([\n]\\s-+\\)?")
                  ;; A toplevel declaration can be followed by a definition
                  ;; (=), a type (::) or (∷), a guard, or a pattern which can
                  ;; either be a variable, a constructor, a parenthesized
                  ;; thingy, or an integer or a string.
                  "\\(" varid "\\|" conid "\\|::\\|∷\\|=\\||\\|\\s(\\|[0-9\"']\\)"))
         (topdecl-var2
          (concat line-prefix "\\(" varid "\\|" conid "\\)\\s-*`\\(" varid "\\)`"))
         (topdecl-bangpat
          (concat line-prefix "\\(" varid "\\)\\s-*!"))
         (topdecl-sym
          (concat line-prefix "\\(" varid "\\|" conid "\\)\\s-*\\(" sym "\\)"))
         (topdecl-sym2 (concat line-prefix "(\\(" sym "\\))"))

         keywords)

    (setq keywords
          `(;; NOTICE the ordering below is significant
            ;;
            ("^<<<<<<< .*$" 0 'font-lock-warning-face t)
            ("^|||||||$" 0 'font-lock-warning-face t) ; "diff3" style
            ("^=======$" 0 'font-lock-warning-face t)
            ("^>>>>>>> .*$" 0 'font-lock-warning-face t)
            ("^#.*$" 0 'font-lock-preprocessor-face t)

            ,@(haskell-font-lock-symbols-keywords)

            (,reservedid 1 haskell-keyword-face)
            (,reservedsym 1 haskell-operator-face)
            ;; Special case for `as', `hiding', `safe' and `qualified', which are
            ;; keywords in import statements but are not otherwise reserved.
            ("\\<import[ \t]+\\(?:\\(safe\\>\\)[ \t]*\\)?\\(?:\\(qualified\\>\\)[ \t]*\\)?\\(?:\"[^\"]*\"[\t ]*\\)?[^ \t\n()]+[ \t]*\\(?:\\(\\<as\\>\\)[ \t]*[^ \t\n()]+[ \t]*\\)?\\(\\<hiding\\>\\)?"
             (1 haskell-keyword-face nil lax)
             (2 haskell-keyword-face nil lax)
             (3 haskell-keyword-face nil lax)
             (4 haskell-keyword-face nil lax))

            (,reservedsym 1 haskell-operator-face)
            ;; Special case for `foreign import'
            ;; keywords in foreign import statements but are not otherwise reserved.
            ("\\<\\(foreign\\)[ \t]+\\(import\\)[ \t]+\\(?:\\(ccall\\|stdcall\\|cplusplus\\|jvm\\|dotnet\\)[ \t]+\\)?\\(?:\\(safe\\|unsafe\\|interruptible\\)[ \t]+\\)?"
             (1 haskell-keyword-face nil lax)
             (2 haskell-keyword-face nil lax)
             (3 haskell-keyword-face nil lax)
             (4 haskell-keyword-face nil lax))

            (,reservedsym 1 haskell-operator-face)
            ;; Special case for `foreign export'
            ;; keywords in foreign export statements but are not otherwise reserved.
            ("\\<\\(foreign\\)[ \t]+\\(export\\)[ \t]+\\(?:\\(ccall\\|stdcall\\|cplusplus\\|jvm\\|dotnet\\)[ \t]+\\)?"
             (1 haskell-keyword-face nil lax)
             (2 haskell-keyword-face nil lax)
             (3 haskell-keyword-face nil lax))

            ;; Toplevel Declarations.
            ;; Place them *before* generic id-and-op highlighting.
            (,topdecl-var  (1 haskell-definition-face))
            (,topdecl-var2 (2 haskell-definition-face))
            (,topdecl-bangpat  (1 haskell-definition-face))
            (,topdecl-sym  (2 haskell-definition-face))
            (,topdecl-sym2 (1 haskell-definition-face))

            ;; These four are debatable...
            ("(\\(,*\\|->\\))" 0 haskell-constructor-face)
            ("\\[\\]" 0 haskell-constructor-face)
            ;; Expensive.
            (,(concat "`" varid "`") 0 haskell-operator-face)
            (,(concat "`" conid "`") 0 haskell-operator-face)
            (,(concat "`" qvarid "`") 0 haskell-operator-face)
            (,(concat "`" qconid "`") 0 haskell-operator-face)
            (,qvarid 0 haskell-default-face)
            (,qconid 0 haskell-constructor-face)
            ;; Expensive.
            (,conid 0 haskell-constructor-face)

            ;; Very expensive.
            (,sym 0 (if (eq (char-after (match-beginning 0)) ?:)
                        haskell-constructor-face
                      haskell-operator-face))

            (haskell-font-lock-find-pragma 0 haskell-pragma-face t)))
    (unless (boundp 'font-lock-syntactic-keywords)
      (cl-case literate
        (bird
         (setq keywords
               `(("^[^>\n].*$" 0 haskell-comment-face t)
                 ,@keywords
                 ("^>" 0 haskell-default-face t))))
        ((latex tex)
         (setq keywords
               `((haskell-font-lock-latex-comments 0 'font-lock-comment-face t)
                 ,@keywords)))))
    keywords))

(defvar haskell-font-lock-latex-cache-pos nil
  "Position of cache point used by `haskell-font-lock-latex-cache-in-comment'.
Should be at the start of a line.")
(make-variable-buffer-local 'haskell-font-lock-latex-cache-pos)

(defvar haskell-font-lock-latex-cache-in-comment nil
  "If `haskell-font-lock-latex-cache-pos' is outside a
\\begin{code}..\\end{code} block (and therefore inside a comment),
this variable is set to t, otherwise nil.")
(make-variable-buffer-local 'haskell-font-lock-latex-cache-in-comment)

(defun haskell-font-lock-latex-comments (end)
  "Sets `match-data' according to the region of the buffer before end
that should be commented under LaTeX-style literate scripts."
  (let ((start (point)))
    (if (= start end)
        ;; We're at the end.  No more to fontify.
        nil
      (if (not (eq start haskell-font-lock-latex-cache-pos))
          ;; If the start position is not cached, calculate the state
          ;; of the start.
          (progn
            (setq haskell-font-lock-latex-cache-pos start)
            ;; If the previous \begin{code} or \end{code} is a
            ;; \begin{code}, then start is not in a comment, otherwise
            ;; it is in a comment.
            (setq haskell-font-lock-latex-cache-in-comment
                  (if (and
                       (re-search-backward
                        "^\\(\\(\\\\begin{code}\\)\\|\\(\\\\end{code}\\)\\)$"
                        (point-min) t)
                       (match-end 2))
                      nil t))
            ;; Restore position.
            (goto-char start)))
      (if haskell-font-lock-latex-cache-in-comment
          (progn
            ;; If start is inside a comment, search for next \begin{code}.
            (re-search-forward "^\\\\begin{code}$" end 'move)
            ;; Mark start to end of \begin{code} (if present, till end
            ;; otherwise), as a comment.
            (set-match-data (list start (point)))
            ;; Return point, as a normal regexp would.
            (point))
        ;; If start is inside a code block, search for next \end{code}.
        (if (re-search-forward "^\\\\end{code}$" end t)
            ;; If one found, mark it as a comment, otherwise finish.
            (point))))))

(defconst haskell-basic-syntactic-keywords
  '(;; Character constants (since apostrophe can't have string syntax).
    ;; Beware: do not match something like 's-}' or '\n"+' since the first '
    ;; might be inside a comment or a string.
    ;; This still gets fooled with "'"'"'"'"'"', but ... oh well.
    ("\\Sw\\('\\)\\([^\\'\n]\\|\\\\.[^\\'\n \"}]*\\)\\('\\)" (1 "|") (3 "|"))
    ;; The \ is not escaping in \(x,y) -> x + y.
    ("\\(\\\\\\)(" (1 "."))
    ;; The second \ in a gap does not quote the subsequent char.
    ;; It's probably not worth the trouble, tho.
    ;; ("^[ \t]*\\(\\\\\\)" (1 "."))
    ;; Deal with instances of `--' which don't form a comment
    ("\\s_\\{3,\\}" (0 (cond ((numberp (nth 4 (syntax-ppss)))
                              ;; There are no such instances inside nestable comments
                              nil)
                             ((string-match "\\`-*\\'" (match-string 0))
                              ;; Sequence of hyphens.  Do nothing in
                              ;; case of things like `{---'.
                              nil)
                             (t "_")))) ; other symbol sequence
    ))

(defconst haskell-bird-syntactic-keywords
  (cons '("^[^\n>]"  (0 "<"))
        haskell-basic-syntactic-keywords))

(defconst haskell-latex-syntactic-keywords
  (append
   '(("^\\\\begin{code}\\(\n\\)" 1 "!")
     ;; Note: buffer is widened during font-locking.
     ("\\`\\(.\\|\n\\)" (1 "!"))               ; start comment at buffer start
     ("^\\(\\\\\\)end{code}$" 1 "!"))
   haskell-basic-syntactic-keywords))

(defcustom haskell-font-lock-haddock (boundp 'font-lock-doc-face)
  "If non-nil try to highlight Haddock comments specially."
  :type 'boolean
  :group 'haskell)

(defvar haskell-font-lock-seen-haddock nil)
(make-variable-buffer-local 'haskell-font-lock-seen-haddock)

(defun haskell-syntactic-face-function (state)
  "`font-lock-syntactic-face-function' for Haskell."
  (cond
   ((nth 3 state) font-lock-string-face) ; as normal
   ;; Else comment.  If it's from syntax table, use default face.
   ((or (eq 'syntax-table (nth 7 state))
        (and (eq haskell-literate 'bird)
             (memq (char-before (nth 8 state)) '(nil ?\n))))
    haskell-literate-comment-face)
   ;; Try and recognize Haddock comments.  From what I gather from its
   ;; documentation, its comments can take the following forms:
   ;; a) {-| ... -}
   ;; b) {-^ ... -}
   ;; c) -- | ...
   ;; d) -- ^ ...
   ;; e) -- ...
   ;; Where `e' is the tricky one: it is only a Haddock comment if it
   ;; follows immediately another Haddock comment.  Even an empty line
   ;; breaks such a sequence of Haddock comments.  It is not clear if `e'
   ;; can follow any other case, so I interpreted it as following only cases
   ;; c,d,e (not a or b).  In any case, this `e' is expensive since it
   ;; requires extra work for each and every non-Haddock comment, so I only
   ;; go through the more expensive check if we've already seen a Haddock
   ;; comment in the buffer.
   ;;
   ;; And then there are also haddock section headers that start with
   ;; any number of stars:
   ;;   -- * ...
   ((and haskell-font-lock-haddock
         (save-excursion
           (goto-char (nth 8 state))
           (or (looking-at "\\(?:{- ?\\|-- \\)[|^*$]")
               (and haskell-font-lock-seen-haddock
                    (looking-at "--")
                    (let ((doc nil)
                          pos)
                      (while (and (not doc)
                                  (setq pos (line-beginning-position))
                                  (forward-comment -1)
                                  (eq (line-beginning-position 2) pos)
                                  (looking-at "--\\([ \\t]*[|^*]\\)?"))
                        (setq doc (match-beginning 1)))
                      doc)))))
    (setq haskell-font-lock-seen-haddock t)
    font-lock-doc-face)
   (t font-lock-comment-face)))

(defconst haskell-font-lock-keywords
  (haskell-font-lock-keywords-create nil)
  "Font lock definitions for non-literate Haskell.")

(defconst haskell-font-lock-bird-literate-keywords
  (haskell-font-lock-keywords-create 'bird)
  "Font lock definitions for Bird-style literate Haskell.")

(defconst haskell-font-lock-latex-literate-keywords
  (haskell-font-lock-keywords-create 'latex)
  "Font lock definitions for LaTeX-style literate Haskell.")

;;;###autoload
(defun haskell-font-lock-choose-keywords ()
  (let ((literate (if (boundp 'haskell-literate) haskell-literate)))
    (cl-case literate
      (bird haskell-font-lock-bird-literate-keywords)
      ((latex tex) haskell-font-lock-latex-literate-keywords)
      (t haskell-font-lock-keywords))))

(defun haskell-font-lock-choose-syntactic-keywords ()
  (let ((literate (if (boundp 'haskell-literate) haskell-literate)))
    (cl-case literate
      (bird haskell-bird-syntactic-keywords)
      ((latex tex) haskell-latex-syntactic-keywords)
      (t haskell-basic-syntactic-keywords))))

(defun haskell-font-lock-defaults-create ()
  "Locally set `font-lock-defaults' for Haskell."
  (set (make-local-variable 'font-lock-defaults)
       '(haskell-font-lock-choose-keywords
         nil nil ((?\' . "w") (?_  . "w")) nil
         (font-lock-syntactic-keywords
          . haskell-font-lock-choose-syntactic-keywords)
         (font-lock-syntactic-face-function
          . haskell-syntactic-face-function)
         ;; Get help from font-lock-syntactic-keywords.
         (parse-sexp-lookup-properties . t))))

;; The main functions.
(defun turn-on-haskell-font-lock ()
  "Turns on font locking in current buffer for Haskell 1.4 scripts.

Changes the current buffer's `font-lock-defaults', and adds the
following variables:

   `haskell-keyword-face'      for reserved keywords and syntax,
   `haskell-constructor-face'  for data- and type-constructors, class names,
                               and module names,
   `haskell-operator-face'     for symbolic and alphanumeric operators,
   `haskell-default-face'      for ordinary code.

The variables are initialised to the following font lock default faces:

   `haskell-keyword-face'      `font-lock-keyword-face'
   `haskell-constructor-face'  `font-lock-type-face'
   `haskell-operator-face'     `font-lock-function-name-face'
   `haskell-default-face'      <default face>

Two levels of fontification are defined: level one (the default)
and level two (more colour).  The former does not colour operators.
Use the variable `font-lock-maximum-decoration' to choose
non-default levels of fontification.  For example, adding this to
.emacs:

  (setq font-lock-maximum-decoration '((haskell-mode . 2) (t . 0)))

uses level two fontification for `haskell-mode' and default level for
all other modes.  See documentation on this variable for further
details.

To alter an attribute of a face, add a hook.  For example, to change
the foreground colour of comments to brown, add the following line to
.emacs:

  (add-hook 'haskell-font-lock-hook
      (lambda ()
          (set-face-foreground 'haskell-comment-face \"brown\")))

Note that the colours available vary from system to system.  To see
what colours are available on your system, call
`list-colors-display' from emacs.

To turn font locking on for all Haskell buffers, add this to .emacs:

  (add-hook 'haskell-mode-hook 'turn-on-haskell-font-lock)

To turn font locking on for the current buffer, call
`turn-on-haskell-font-lock'.  To turn font locking off in the current
buffer, call `turn-off-haskell-font-lock'.

Bird-style literate Haskell scripts are supported: If the value of
`haskell-literate-bird-style' (automatically set by the Haskell mode
of Moss&Thorn) is non-nil, a Bird-style literate script is assumed.

Invokes `haskell-font-lock-hook' if not nil."
  (haskell-font-lock-defaults-create)
  (run-hooks 'haskell-font-lock-hook)
  (turn-on-font-lock))

(defun turn-off-haskell-font-lock ()
  "Turns off font locking in current buffer."
  (font-lock-mode -1))

(defun haskell-fontify-as-mode (text mode)
  "Fontify TEXT as MODE, returning the fontified text."
  (with-temp-buffer
    (funcall mode)
    (insert text)
    (if (fboundp 'font-lock-ensure)
        (font-lock-ensure)
      (with-no-warnings (font-lock-fontify-buffer)))
    (buffer-substring (point-min) (point-max))))

;; Provide ourselves:

(provide 'haskell-font-lock)

;; Local Variables:
;; tab-width: 8
;; End:

;;; haskell-font-lock.el ends here
