;;; -*- coding: utf-8; -*-
;; coq-unicode-tokens.el --- (No) Tokens for Unicode Tokens package
;;
;; Copyright(C) 2008, 2009 David Aspinall / LFCS Edinburgh
;; Author:    David Aspinall <David.Aspinall@ed.ac.uk>
;;
;; This file is loaded by `proof-unicode-tokens.el'.
;;
;; It sets the variables defined at the top of unicode-tokens.el,
;; unicode-tokens-<foo> is set from coq-<foo>.  See the corresponding
;; variable for documentation.
;;
;; For Coq, there is no dedicated token syntax, it's probably
;; preferable to use UTF-8 notation directly (see utf8.v).  
;; 
;; On the other hand, for easily portable files, one can fix
;; ordinary character sequences as tokens, like the old X-Symbol
;; configuration for Coq did.
;;
;; The configuration here is an example which (for added confusion)
;; does both things.  Keyboard shortcuts get replaced by "real"
;; Unicode characters, whereas ordinary character sequences are
;; displayed as those characters.
;;
;; Recommended ways to work: 
;;
;;   1) UTF-8 buffers:  ☑ Show Symbol Tokens  (ON)
;;			☑ Enable Shortcuts    (ON)
;;		        
;;   2) ASCII buffers:  ☐ Enable Shortcuts    (OFF)
;;			☐ Show Symbol Tokens  (OFF)
;;
;; The (confusing!) default is to enable shortcuts and display tokens.
;; Use Tokens -> Highlight Real Unicode Chars to help understand the
;; buffer contents.  Hovering on a token shows its underlying text.

(require 'proof-unicode-tokens)

(defconst coq-token-format "%s")	; plain tokens
(defconst coq-token-match nil)
(defconst coq-hexcode-match nil)

(defun coq-unicode-tokens-set (sym val)
  "Change a Unicode Tokens configuration variable and restart."
  (set-default sym val)
  (when (featurep 'coq-unicode-tokens) ; not during loading
    (proof-unicode-tokens-configure)))

(defcustom coq-token-symbol-map
  '(;; Greek letters
    ("alpha" "α")
    ("beta" "β")
    ("gamma" "γ")
    ("delta" "δ")
    ("epsilon" "ε")
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
    ("phi" "ϕ")
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
    ("Omega" "Ω")
    ;; logic
    ("forall" "∀")
    ("exists" "∃")
    ("nat" "ℕ" type)
    ("complex" "ℂ" type)
    ("real" "ℝ" type)
    ("int" "ℤ" type)
    ("rat" "ℚ" type)
    ("bool" "B" underline type)
    ("false" "false" bold sans)
    ("true" "true" bold sans)

    ;; example tokens used in Benjamin C. Pierce et al's 
    ;; Software Foundations course
    ("WHILE" "WHILE" bold sans)
    ("DO" "DO" bold sans)
    ("END" "END" bold sans)
    ("SKIP" "SKIP" bold sans)
    ("THEN" "THEN" bold sans)
    ("ELSE" "ELSE" bold sans)
    ("IFB" "IFB" bold sans)
    ("FI" "FI" bold sans)
    ("{{" "⦃" bold)
    ("}}" "⦄" bold)

    ;; symbols without utf8.v  (but also without context)
    ("lhd" "⊲")
    ("rhd" "⊳")
    ("<=" "≤")
    (">=" "≥")
    ("=>" "⇒")
    ("->" "→")  ; or ⟶ or ⟹ if you prefer
    ("<-" "←")  ; or ⟵ or ⟸ 
    ("<->" "↔") ; or ⟷ ...
    ("++" "⧺")
    ("<<" "《")
    (">>" "》")

    ;; Equivalence
    ("===" "≡") ; equiv
    ("=/=" "≢")  ; complement equiv
    ("=~=" "≅") ; pequiv
    ("==b" "≡") ; NB: same presentation
    ("<>b" "≢") ; NB: same presentation
    
    ;; ("==" "≡")  ; Setoid equiv (NB: same presentation, pot confusing)

    ("-->" "⟹-") ; Morphisms
    ("++>" "⟹+") ; 
    ("==>" "⟹") ; 

    (":=" "≔")
    ("|-" "⊢")
    ("<>" "≠")
    ("-|" "⊣")
    ("\\/" "∨")
    ("/\\" "∧")
    ("~"  "¬")
    
    ;; A dirty hack for the goals window, shouldn't be input syntax!
    ("============================" 
     "⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯" 
     bold tactical)
    )
  ;; an alist of token name, unicode char sequence
  "Table mapping Coq tokens to Unicode strings.

You can adjust this table to add entries, or to change entries for
glyphs that not are available in your Emacs or chosen font.

When a file is visited, tokens are replaced by the strings
in this table.  When the file is saved, the reverse is done.
The string mapping can be anything, but should be such that
tokens can be uniquely recovered from a decoded text; otherwise
results will be undefined when files are saved."
  :type 'unicode-tokens-token-symbol-map
  :set 'coq-unicode-tokens-set
  :group 'coq
  :tag "Coq Unicode Token Mapping")

(defcustom coq-shortcut-alist
  '(; short cut, REAL unicode string
    ("<>" . "⋄")
    ("|>" . "⊳")
    ("\\/" . "∨")
    ("/\\" . "∧")
    ("+O" . "⊕")
    ("-O" . "⊖")
    ("xO" . "⊗")
    ("/O" . "⊘")
    ;(".O" . "⊙") ; bad interaction with electric terminatore and double hit terminator
    ("|+" . "†")
    ("|++" . "‡")
    ("<=" . "≤")
    ("|-" . "⊢")
    (">=" . "≥")
    ("-|" . "⊣")
    ("||" . "∥")
    ("==" . "≡")
    ("~=" . "≃")
    ("~~~" . "≍")
    ("~~" . "≈")
    ("~==" . "≅")
    ("|<>|" . "⋈")
    ("|=" . "⊨")
    ("=." . "≐")
    ("_|_" . "⊥")
    ("</" . "≮")
    (">=/" . "≱")
    ("=/" . "≠")
    ("==/" . "≢")
    ("~/" . "≁")
    ("~=/" . "≄")
    ("~~/" . "≉")
    ("~==/" . "≇")
    ("<-" . "←")
    ("<=" . "⇐")
    ("->" . "→")
    ("=>" . "⇒")
    ("<->" . "↔")
    ("<=>" . "⇔")
    ("|->" . "↦")
    ("<--" . "⟵")
    ("<==" . "⟸")
    ("-->" . "⟶")
    ("==>" . "⟹")
    ("<==>" . "⟷")
    ("|-->" . "⟼")
    ("<--" . "←⎯")
    ("<-->" . "⟷")
    ("<<" . "⟪")
    ("[|" . "⟦")
    (">>" . "⟫")
    ("|]" . "⟧")
    ("``" . "”")
    ("''" . "“")
    ("--" . "–")
    ("---" . "—")
    ("''" . "″")
    ("'''" . "‴")
    ("''''" . "⁗")
    (":=" . "≔")
    ;; some word shortcuts, started with backslash otherwise
    ;; too annoying, perhaps.
    ("\\int" . "ℤ")
    ("\\rat" . "ℚ")
    ("\\complex" . "ℂ")
    ("\\euro" . "€")
    ("\\yen" . "¥")
    ("\\cent" . "¢"))
  "Shortcut key sequence table for Unicode strings.

You can adjust this table to add more entries, or to change entries for
glyphs that not are available in your Emacs or chosen font.

These shortcuts are only used for input; no reverse conversion is
performed.  This means that the target strings need to have a defined
meaning to be useful."
  :type '(repeat (cons (string :tag "Shortcut sequence")
		       (string :tag "Unicode string")))
  :set 'coq-unicode-tokens-set
  :group 'coq
  :tag "Coq Unicode Input Shortcuts")


;;
;; Controls
;;

(defconst coq-control-char-format-regexp
  ;; FIXME: fix Coq identifier syntax below
  "\\(\s*%s\s*\\)\\([a-zA-Z0-9']+\\)")

(defconst coq-control-char-format " %s ")

(defconst coq-control-characters
  '(("Subscript" "__" sub)
    ("Superscript" "^^" sup)))

(defconst coq-control-region-format-regexp "\\(\s*%s\{\\)\\([^}]*\\)\\(\}\s*\\)")

(defconst coq-control-regions
  '(("Subscript" "," "" sub)
    ("Superscript" "^" "" sup)
    ("Bold" "BOLD" "" bold)
    ("Italic" "ITALIC" "" italic)
    ("Script" "SCRIPT" "" script)
    ("Frakt"  "FRACT" "" frakt)
    ("Roman"  "ROMAN" "" serif)))







(provide 'coq-unicode-tokens)

;;; coq-unicode-tokens.el ends here
