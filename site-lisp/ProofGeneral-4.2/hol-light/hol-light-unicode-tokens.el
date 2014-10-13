;;; -*- coding: utf-8; -*-
;; coq-unicode-tokens.el --- (No) Tokens for Unicode Tokens package
;;
;; Copyright(C) 2012 David Aspinall / University of Edinburgh
;; Author:    David Aspinall <David.Aspinall@ed.ac.uk>
;;
;; This file is loaded by `proof-unicode-tokens.el'.
;;
;; It sets the variables defined at the top of unicode-tokens.el,
;; unicode-tokens-<foo> is set from hol-light-<foo>.  See the corresponding
;; variable for documentation.
;;
;; For HOL Light, there is no dedicated token syntax, we simply
;; define replacements for common ASCII sequences.
;; 
;; FIXME TODO: 
;;  - only do it for quoted text
;;  - fix unicode tokens sorting so longs tokens handled first (broken?)
;;      <=> not <= >

(require 'proof-unicode-tokens)

(defconst hol-light-token-format "%s")	; plain tokens
(defconst hol-light-token-match nil)
(defconst hol-light-hexcode-match nil)

(defun hol-light-unicode-tokens-set (sym val)
  "Change a Unicode Tokens configuration variable and restart."
  (set-default sym val)
  (when (featurep 'hol-light-unicode-tokens) ; not during loading
    (proof-unicode-tokens-configure)))

(defcustom hol-light-token-symbol-map
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
    (":num" ":ℕ" type) ;; ?
    (":complex" ":ℂ" type)
    (":real" ":ℝ" type)
    (":int" ":ℤ" type)
    ("rat" "ℚ" type)
    ("bool" "B" underline type)
    ("false" "false" bold sans)
    ("true" "true" bold sans)

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
  :set 'hol-light-unicode-tokens-set
  :group 'coq
  :tag "Coq Unicode Token Mapping")

(defcustom hol-light-shortcut-alist
  '(; short cut, REAL unicode string
    ("<>" . "⋄")
    ("|>" . "⊳")
    ("\\/" . "∨")
    ("/\\" . "∧")
    ("+O" . "⊕")
    ("-O" . "⊖")
    ("xO" . "⊗")
    ("/O" . "⊘")
    (".O" . "⊙")
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
  :set 'hol-light-unicode-tokens-set
  :group 'coq
  :tag "Coq Unicode Input Shortcuts")


;;
;; Controls
;;

(defconst hol-light-control-char-format-regexp
  ;; FIXME: fix Coq identifier syntax below
  "\\(\s*%s\s*\\)\\([a-zA-Z0-9']+\\)")

(defconst hol-light-control-char-format " %s ")

(defconst hol-light-control-characters
  '(("Subscript" "__" sub)
    ("Superscript" "^^" sup)))

(defconst hol-light-control-region-format-regexp "\\(\s*%s\{\\)\\([^}]*\\)\\(\}\s*\\)")

(defconst hol-light-control-regions
  '(("Subscript" "," "" sub)
    ("Superscript" "^" "" sup)
    ("Bold" "BOLD" "" bold)
    ("Italic" "ITALIC" "" italic)
    ("Script" "SCRIPT" "" script)
    ("Frakt"  "FRACT" "" frakt)
    ("Roman"  "ROMAN" "" serif)))


(provide 'hol-light-unicode-tokens)

;;; hol-light-unicode-tokens.el ends here
