;;; -*- coding: utf-8; -*-
;; isar-unicode-tokens.el --- Tokens for Unicode Tokens package
;;
;; Copyright(C) 2008, 2009 David Aspinall / LFCS Edinburgh
;; Author:    David Aspinall <David.Aspinall@ed.ac.uk>
;;
;; This file is loaded by proof-auxmodes.el for proof-unicode-tokens.el.
;;
;; It sets the variables defined at the top of unicode-tokens.el,
;; unicode-tokens-<foo> is set from isar-<foo>.  See the corresponding
;; variable for documentation.
;;


(require 'cl)				; for-loop

(eval-when (compile)
  (require 'unicode-tokens)	    ; it's loaded dynamically at runtime
  (require 'proof-unicode-tokens))  ; that file loads us at runtime

;;
;; Customization
;;

(defgroup isabelle-tokens nil
  "Variables which configure Isabelle tokens for Unicode Tokens mode."
  :group 'isabelle
  :prefix "isar-")

(defun isar-set-and-restart-tokens (sym val)
  "Function to restart Unicode Tokens when a token value is adjusted."
  (set-default sym val)
  (when (featurep 'isar-unicode-tokens) ; not during loading
    (isar-init-token-symbol-map)
    (isar-init-shortcut-alists)
    (if (featurep 'unicode-tokens)
	(unicode-tokens-initialise))))

;;
;; Controls
;;

(defconst isar-control-region-format-regexp
  "\\(\\\\<\\^%s>\\)\\(.*?\\)\\(\\\\<\\^%s>\\)")

(defconst isar-control-char-format-regexp
  (concat
   "\\(\\\\<\\^%s>\\)\\("
   "\\(?:\\\\<[A-Za-z]+>\\|[^\\]\\)" ; cf isar-ext-first
   "\\)"))

(defconst isar-control-char-format	   "\\<^%s>")
(defconst isar-control-region-format-start "\\<^%s>")
(defconst isar-control-region-format-end   "\\<^%s>")


(defcustom isar-control-characters
  '(("Subscript" "sub" sub)
    ("Id subscript" "isub" sub)
    ("Superscript" "sup" sup)
    ("Id superscript" "isup" sup)
    ("Loc" "loc" keyword)
    ("Constant" "const" keyword)
    ("Bold" "bold" bold)
    ;; unofficial/unsupported:
    ("Italic" "italic" italic))
  "Control character tokens for Isabelle."
  :group 'isabelle-tokens
  :set 'isar-set-and-restart-tokens)

(defcustom isar-control-regions
  '(("Subscript" "bsub" "esub" sub)
    ("Superscript" "bsup" "esup" sup)
    ;; unofficial/unsupported:
    ("Id subscript" "bisub" "eisub" sub)
    ("Id superscript" "bisup" "eisup" sup)
    ("Bold" "bbold" "ebold" bold)
    ("Italic" "bitalic" "eitalic" italic)
    ("Script" "bscript" "escript" script)
    ("Frakt" "bfrakt" "efrakt" frakt)
    ("Roman" "bserif" "eserif" serif)
    ("Sans" "bsans" "esans" sans)
    ("Overline" "boverline" "eoverline" overline)
    ("Underline" "bunderline" "eunderline" underline)
    ("Big"   "bbig" "ebig" big)
    ("Small" "bsmall" "esmall" small)
;    ("Large symbols" "bbigsyms" "ebigsyms" large-symbols)
    )
  "Control sequence tokens for Isabelle."
  :group 'isabelle-tokens
  :set 'isar-set-and-restart-tokens)

;;
;; Symbols
;;

(defconst isar-token-format "\\<%s>")

;(defconst isar-token-variant-format-regexp
;  "\\\\<\\(%s\\)\\([:][a-zA-Z0-9]+\\)?>") ; syntax change required
(defconst isar-token-variant-format-regexp
  "\\\\<\\(%s\\)[0-9]*>") ; unofficial interpretation of usual syntax

(defcustom isar-greek-letters-tokens
  '(("alpha" "α")
    ("beta" "β")
    ("gamma" "γ")
    ("delta" "δ")
    ("epsilon" "ε") ; varepsilon (some is epsilon), although PG can use dups
    ("zeta" "ζ")
    ("eta" "η")
    ("theta" "θ")
    ("iota" "ι")
    ("kappa" "κ")
    ("lambda" "λ")
    ("mu" "μ")
    ("nu" "ν")
    ("xi" "ξ")
    ("pi" "π")
    ("rho" "ρ")
    ("sigma" "σ")
    ("tau" "τ")
    ("upsilon" "υ")
    ("phi" "φ")
    ("chi" "χ")
    ("psi" "ψ")
    ("omega" "ω")
    ("Gamma" "Γ")
    ("Delta" "Δ")
    ("Theta" "Θ")
    ("Lambda" "Λ")
    ("Xi" "Ξ")
    ("Pi" "Π")
    ("Sigma" "Σ")
    ("Upsilon" "Υ")
    ("Phi" "Φ")
    ("Psi" "Ψ")
    ("Omega" "Ω"))
  "Greek letter token map for Isabelle."
  :type 'unicode-tokens-token-symbol-map
  :group 'isabelle-tokens
  :set 'isar-set-and-restart-tokens)

(defcustom isar-misc-letters-tokens
  '(("bool" "B" bold underline)
    ("complex" "ℂ")
    ("nat" "ℕ")
    ("rat" "ℚ")
    ("real" "ℝ")
    ("int" "ℤ"))
  "Miscellaneous letter token map for Isabelle."
  :type 'unicode-tokens-token-symbol-map
  :group 'isabelle-tokens
  :set 'isar-set-and-restart-tokens)

(defcustom isar-symbols-tokens
  '(("leftarrow" "←")
    ("rightarrow" "→")
    ("Leftarrow" "⇐")
    ("Rightarrow" "⇒")
    ("leftrightarrow" "↔")
    ("Leftrightarrow" "⇔")
    ("mapsto" "↦")
    ("longleftarrow" "⟵")
    ("Longleftarrow" "⟸")
    ("longrightarrow" "⟶")
    ("Longrightarrow" "⟹")
    ("longleftrightarrow" "⟷")
    ("Longleftrightarrow" "⟺")
    ("longmapsto" "⟼")
    ("midarrow" "–") ; #x002013 en dash
    ("Midarrow" "‗") ; #x002017 double low line (not mid)
    ("hookleftarrow" "↩")
    ("hookrightarrow" "↪")
    ("leftharpoondown" "↽")
    ("rightharpoondown" "⇁")
    ("leftharpoonup" "↼")
    ("rightharpoonup" "⇀")
    ("rightleftharpoons" "⇌")
    ("leadsto" "↝")
    ("downharpoonleft" "⇃")
    ("downharpoonright" "⇂")
    ("upharpoonleft" "↿")  ;;
    ("upharpoonright" "↾") ;; overlaps restriction
    ("restriction" "↾")    ;; same as above
    ("Colon" "∷")
    ("up" "↑")
    ("Up" "⇑")
    ("down" "↓")
    ("Down" "⇓")
    ("updown" "↕")
    ("Updown" "⇕")
    ("langle" "⟨")
    ("rangle" "⟩")
    ("lceil" "⌈")
    ("rceil" "⌉")
    ("lfloor" "⌊")
    ("rfloor" "⌋")
    ("lparr" "⦇")
    ("rparr" "⦈")
    ("lbrakk" "⟦")
    ("rbrakk" "⟧")
    ("lbrace" "⦃")
    ("rbrace" "⦄")
    ("guillemotleft" "«")
    ("guillemotright" "»")
    ("bottom" "⊥")
    ("top" "⊤")
    ("and" "∧")
    ("And" "⋀")
    ("or" "∨")
    ("Or" "⋁")
    ("forall" "∀")
    ("exists" "∃")
    ("nexists" "∄")
    ("not" "¬")
    ("box" "□")
    ("diamond" "◇")
    ("turnstile" "⊢")
    ("Turnstile" "⊨")
    ("tturnstile" "⊩")
    ("TTurnstile" "⊫")
    ("stileturn" "⊣")
    ("surd" "√")
    ("le" "≤")
    ("ge" "≥")
    ("lless" "≪")
    ("ggreater" "≫")
    ("lesssim" "⪍")
    ("greatersim" "⪎")
    ("lessapprox" "⪅")
    ("greaterapprox" "⪆")
    ("in" "∈")
    ("notin" "∉")
    ("subset" "⊂")
    ("supset" "⊃")
    ("subseteq" "⊆")
    ("supseteq" "⊇")
    ("sqsubset" "⊏")
    ("sqsupset" "⊐")
    ("sqsubseteq" "⊑")
    ("sqsupseteq" "⊒")
    ("inter" "∩")
    ("Inter" "⋂")
    ("union" "∪")
    ("Union" "⋃")
    ("squnion" "⊔")
    ("Squnion" "⨆")
    ("sqinter" "⊓")
    ("Sqinter" "⨅")
    ("setminus" "∖")
    ("propto" "∝")
    ("uplus" "⊎")
    ("Uplus" "⨄")
    ("noteq" "≠")
    ("sim" "∼")
    ("doteq" "≐")
    ("simeq" "≃")
    ("approx" "≈")
    ("asymp" "≍")
    ("cong" "≅")
    ("smile" "⌣")
    ("equiv" "≡")
    ("frown" "⌢")
    ("Join" "⨝")
    ("bowtie" "⋈")
    ("prec" "≺")
    ("succ" "≻")
    ("preceq" "≼")
    ("succeq" "≽")
    ("parallel" "∥")
    ("bar" "¦")
    ("plusminus" "±")
    ("minusplus" "∓")
    ("times" "×")
    ("div" "÷")
    ("cdot" "⋅")
    ("star" "⋆")
    ("bullet" "∙")
    ("circ" "∘")
    ("dagger" "†")
    ("ddagger" "‡")
    ("lhd" "⊲")
    ("rhd" "⊳")
    ("unlhd" "⊴")
    ("unrhd" "⊵")
    ("triangleleft" "◁")
    ("triangleright" "▷")
    ("triangle" "▵") ; or △
    ("triangleq" "≜")
    ("oplus" "⊕")
    ("Oplus" "⨁")
    ("otimes" "⊗")
    ("Otimes" "⨂")
    ("odot" "⊙")
    ("Odot" "⨀")
    ("ominus" "⊖")
    ("oslash" "⊘")
    ("dots" "…")
    ("cdots" "⋯")
    ("Sum" "∑")
    ("Prod" "∏")
    ("Coprod" "∐")
    ("infinity" "∞")
    ("integral" "∫")
    ("ointegral" "∮")
    ("clubsuit" "♣")
    ("diamondsuit" "♢")
    ("heartsuit" "♡")
    ("spadesuit" "♠")
    ("aleph" "ℵ")
    ("emptyset" "∅")
    ("nabla" "∇")
    ("partial" "∂")
    ("Re" "ℜ")
    ("Im" "ℑ")
    ("flat" "♭")
    ("natural" "♮")
    ("sharp" "♯")
    ("angle" "∠")
    ("copyright" "©")
    ("registered" "®")
    ("hyphen" "‐")
    ("inverse" "¯¹") ; X-Symb: just "¯"
    ("onesuperior" "¹")
    ("twosuperior" "²")
    ("threesuperior" "³")
    ("onequarter" "¼")
    ("onehalf" "½")
    ("threequarters" "¾")
    ("ordmasculine" "º")
    ("ordfeminine" "ª")
    ("section" "§")
    ("paragraph" "¶")
    ("exclamdown" "¡")
    ("questiondown" "¿")
    ("euro" "€")
    ("pounds" "£")
    ("yen" "¥")
    ("cent" "¢")
    ("currency" "¤")
    ("degree" "°")
    ("amalg" "⨿")
    ("mho" "℧")
    ("lozenge" "◊")
    ("wp" "℘")
    ("wrong" "≀")  ;; #x002307
    ("struct" "⋄") ;; #x0022c4
    ("acute" "´")
    ("index" "ı")
    ("dieresis" "¨")
    ("cedilla" "¸")
    ("hungarumlaut" "ʺ")
    ("spacespace" " ")  ;; #x002001
    ("module" "⟨module⟩" bold)
    ("some" "ϵ"))
  "Symbol token map for Isabelle.  The standard set of Isabelle symbols."
  :type 'unicode-tokens-token-symbol-map
  :group 'isabelle-tokens
  :set 'isar-set-and-restart-tokens)

(defcustom isar-extended-symbols-tokens
  '(("stareq" "≛")
    ("defeq" "≝")
    ("questioneq" "≟")
    ("vartheta" "ϑ")
    ; ("o" "ø")
    ("varpi" "ϖ")
    ("varrho" "ϱ")
    ("varsigma" "ς")
    ("varphi" "ϕ")
    ("hbar" "ℏ")
    ("ell" "ℓ")
    ("ast" "∗")

    ("bigcirc" "◯")
    ("bigtriangleup" "△")
    ("bigtriangledown" "▽")
    ("ni" "∋")
    ("mid" "∣")
    ("notlt" "≮")
    ("notle" "≰")
    ("notprec" "⊀")
    ("notpreceq" "⋠")
    ("notsubset" "⊄")
    ("notsubseteq" "⊈")
    ("notsqsubseteq" "⋢")
    ("notgt" "≯")
    ("notge" "≱")
    ("notsucc" "⊁")
    ("notsucceq" "⋡")
    ("notsupset" "⊅")
    ("notsupseteq" "⊉")
    ("notsqsupseteq" "⋣")
    ("notequiv" "≢")
    ("notsim" "≁")
    ("notsimeq" "≄")
    ("notapprox" "≉")
    ("notcong" "≇")
    ("notasymp" "≭")
    ("nearrow" "↗")
    ("searrow" "↘")
    ("swarrow" "↙")
    ("nwarrow" "↖")
    ("vdots" "⋮")
    ("ddots" "⋱")
    ("closequote" "’")
    ("openquote" "‘")
    ("opendblquote" "”")
    ("closedblquote" "“")
    ("emdash" "—")
    ("prime" "′")
    ("doubleprime" "″")
    ("tripleprime" "‴")
    ("quadrupleprime" "⁗")
    ("nbspace" " ")
    ("thinspace" " ")
    ("notni" "∌")
    ("colonequals" "≔")
    ("foursuperior" "⁴")
    ("fivesuperior" "⁵")
    ("sixsuperior" "⁶")
    ("sevensuperior" "⁷")
    ("eightsuperior" "⁸")
    ("ninesuperior" "⁹"))
  "Extended symbols token map for Isabelle.  These are not defined standardly."
  :type 'unicode-tokens-token-symbol-map
  :group 'isabelle-tokens
  :set 'isar-set-and-restart-tokens)

(defun isar-try-char (charset code1 code2)
  (and (charsetp charset) ; prevent error
       (char-to-string (make-char charset code1 code2))))

(defcustom isar-symbols-tokens-fallbacks
  `(;; Faked long symbols
    ("longleftarrow" "←-")
    ("Longleftarrow" "⇐–")
    ("longrightarrow" "–→")
    ("Longrightarrow" "–⇒")
    ("longleftrightarrow" "←→")
    ("Longleftrightarrow" "⇐⇒")
    ("longmapsto" "❘→")
    ;; bracket composition alternatives
    ("lparr" "(|")
    ("rparr" "|)")
    ;; an example of using characters from another charset.
    ;; to expand this table, see output of M-x list-charset-chars
    ("lbrakk" ,(isar-try-char 'japanese-jisx0208 #x22 #x5A))
    ("rbrakk" ,(isar-try-char 'japanese-jisx0208 #x22 #x5A))
    ("lbrakk" "[|")
    ("rbrakk" "|]")
    ("lbrace" "{|")
    ("rbrace" "|}"))
  "Fallback alternatives to `isar-symbols-tokens'.
The first displayable composition will be displayed to replace the
tokens."
  :type 'unicode-tokens-token-symbol-map
  :group 'isabelle-tokens
  :set 'isar-set-and-restart-tokens)

(defcustom isar-bold-nums-tokens
  '(("zero" "0" bold)
    ("one" "1" bold)
    ("two" "2" bold)
    ("three" "3" bold)
    ("four" "4" bold)
    ("five" "5" bold)
    ("six" "6" bold)
    ("seven" "7" bold)
    ("eight" "8" bold)
    ("nine" "9" bold))
  "Tokens for bold numerals."
  :type 'unicode-tokens-token-symbol-map
  :group 'isabelle-tokens
  :set 'isar-set-and-restart-tokens)

(defun isar-map-letters (f1 f2 &rest symbs)
  (loop for x below 26
	for c = (+ 65 x)
	collect
	(cons (funcall f1 c) (cons (funcall f2 c) symbs))))

(defconst isar-script-letters-tokens ; \<A> \<B> ...
  (isar-map-letters (lambda (x) (format "%c" x))
		    (lambda (x) (format "%c" x))
		    'script))

(defconst isar-roman-letters-tokens ; \<a> \<b> ...
  (isar-map-letters (lambda (x) (downcase (format "%c" x)))
		    (lambda (x) (downcase (format "%c" x)))
		    'serif))

(defconst isar-fraktur-uppercase-letters-tokens ; \<AA> \<BB> ..
  (isar-map-letters (lambda (x) (format "%c%c" x x))
		    (lambda (x) (format "%c" x))
		    'frakt))

(defconst isar-fraktur-lowercase-letters-tokens ; \<AA> \<BB> ..
  (isar-map-letters (lambda (x) (downcase (format "%c%c" x x)))
		    (lambda (x) (downcase (format "%c" x)))
		    'frakt))

(defcustom isar-token-symbol-map nil
  "Table mapping Isabelle symbol token names to Unicode strings.
See `unicode-tokens-token-symbol-map'.

You can adjust this table to change the default entries.

Each element is a list

  (TOKNAME COMPOSITION FONTSYMB ...)

COMPOSITION is usually a string, perhaps containing Unicode characters.
For Isabelle, the token TOKNAME is made into the token \\<TOKNAME>."
  :type 'unicode-tokens-token-symbol-map
  :group 'isabelle
  :set 'isar-set-and-restart-tokens
  :tag "Isabelle Unicode Token Mapping")

(defcustom isar-user-tokens nil
  "User-defined additions to `isar-token-symbol-map'.

Each element is a list

  (TOKNAME COMPOSITION FONTSYMB ...)

COMPOSITION is usually a string, perhaps containing Unicode characters.
For Isabelle, the token TOKNAME is made into the token \\<TOKNAME>."
  :type 'unicode-tokens-token-symbol-map
  :group 'isabelle
  :set 'isar-set-and-restart-tokens
  :tag "User extensions for Isabelle Token Mapping")

(defun isar-init-token-symbol-map ()
  "Initialise the default value for `unicode-tokens-token-symbol-map'."
  (custom-set-default 'isar-token-symbol-map
		      (append
		       isar-symbols-tokens
		       isar-extended-symbols-tokens
		       isar-user-tokens
		       isar-misc-letters-tokens
		       isar-greek-letters-tokens
		       isar-bold-nums-tokens
		       isar-script-letters-tokens
		       isar-roman-letters-tokens
		       isar-fraktur-uppercase-letters-tokens
		       isar-fraktur-lowercase-letters-tokens
		       isar-user-tokens
		       isar-symbols-tokens-fallbacks)))

(isar-init-token-symbol-map)



;;
;; Shortcuts
;;

(defcustom isar-symbol-shortcuts
  '(("\\/" . "\\<or>")
    ("/\\" . "\\<and>")
    ("+O" . "\\<oplus>")
    ("-O" . "\\<ominus>")
    ("xO" . "\\<otimes>")
    ("/O" . "\\<oslash>")
    (".O" . "\\<odot>")
    ("|+" . "\\<dagger>")
    ("|++" . "\\<ddagger>")
    ("<=" . "\\<le>")
    ("|-" . "\\<turnstile>")
    (">=" . "\\<ge>")
    ("-|" . "\\<stileturn>")
    ("||" . "\\<parallel>")
    ("==" . "\\<equiv>")
    ("~=" . "\\<noteq>")
    ("~:" . "\\<notin>")
    ("~~~" . "\\<notapprox>")
    ("~~" . "\\<approx>")
    ("~==" . "\\<cong>")
    ("|<>|" . "\\<bowtie>")
    ("|=" . "\\<Turnstile>")
    ("=." . "\\<doteq>")
    ("_|_" . "\\<bottom>")
    ("</" . "\\<notle>")
    ("~>=" . "\\<notge>")
    ("==/" . "\\<notequiv>")
    ("~/" . "\\<notsim>")
    ("~=/" . "\\<notsimeq>")
    ("~~/" . "\\<notsimeq>")
    ("<-" . "\\<leftarrow>")
    ("<=" . "\\<Leftarrow>")
    ("->" . "\\<rightarrow>")
    ("=>" . "\\<Rightarrow>")
    ("<->" . "\\<leftrightarrow>")
    ("<=>" . "\\<Leftrightarrow>")
    ("|->" . "\\<mapsto>")
    ("<--" . "\\<longleftarrow>")
    ("<==" . "\\<Longleftarrow>")
    ("-->" . "\\<longrightarrow>")
    ("==>" . "\\<Longrightarrow>")
    ("<==>" . "\\<Longleftrightarrow>")
    ("|-->" . "\\<longmapsto>")
    ("<->" . "\\<longleftrightarrow>")
    ("<<" . "\\<guillemotleft>")
    (">>" . "\\<guillemotright>")
    ("<>" . "\\<diamond>")
    ("[|" . "\\<lbrakk>")
    ("|]" . "\\<rbrakk>")
    ("{|" . "\\<lbrace>")
    ("|}" . "\\<rbrace>")
    ("(|" . "\\<lparr>")
    ("|)" . "\\<rparr>")
    ;; useful for unicode-tokens-replace-shortcuts
    ("ALL" . "\\<forall>")
    ("EX"  . "\\<exists>")
    ("!!"  . "\\<And>")
    ;; TODO: put these into replacement shortcuts, perhaps
    ;; ("~"  . "\\<not>")
    ;; ("!"  . "\\<forall>")
    ;; ("?"  . "\\<exists>")
    ;; extra misc, switch them off if you don't like them
    ;("|>" . "\\<triangleright>") ; clashes with ML parsing combinator
    ("<|" . "\\<triangleleft>"))
  "Shortcut key sequence table for symbol tokens input.
See `unicode-tokens-shortcut-alist'."
    :type 'unicode-tokens-shortcut-alist
    :set 'isar-set-and-restart-tokens
    :group 'isabelle
    :tag "Isabelle symbol shortcuts")

(defcustom isar-shortcut-alist nil
  "Shortcut key sequence table for token input.
See `unicode-tokens-shortcut-alist'."
  :type 'unicode-tokens-shortcut-alist
  :set 'isar-set-and-restart-tokens
  :group 'isabelle
  :tag "Isabelle Unicode Input Shortcuts")

(defun isar-init-shortcut-alists ()
  "Set defaults for `isar-shortcut-alist' and `isar-shortcut-replacement-alist'."
  (custom-set-default 'isar-shortcut-alist
		      (append
		       isar-symbol-shortcuts
		       ;; LaTeX-like syntax for symbol names, easier to type
		       (mapcar
			(lambda (tokentry)
			  (cons (concat "\\" (car tokentry))
				(format isar-token-format (car tokentry))))
			(append isar-greek-letters-tokens
				isar-symbols-tokens)))))
  ;; todo: allow shortcuts for replacements to be a different list
  ;; (setq unicode-tokens-shortcut-replacement-alist nil))

(isar-init-shortcut-alists)

;;
;; To generate special menu entries
;;

(defconst isar-tokens-customizable-variables
  '(("Symbols" isar-symbols-tokens)
    ("Extended Symbols" isar-extended-symbols-tokens)
    ("User Tokens" isar-user-tokens)
    ("Misc Letters" isar-misc-letters-tokens)
    ("Greek Letters" isar-greek-letters-tokens)
    ("Fallbacks" isar-symbols-tokens-fallbacks)
    ("Shortcuts" isar-symbol-shortcuts)))


;;
;; prover symbol support
;;

(eval-after-load "isar"
  '(setq
    proof-tokens-activate-command
    (isar-markup-ml "change print_mode (insert (op =) \"xsymbols\")")
    proof-tokens-deactivate-command
    (isar-markup-ml "change print_mode (remove (op =) \"xsymbols\")")))



(provide 'isar-unicode-tokens)

;;; isar-unicode-tokens.el ends here
