;;; maths-menu.el --- insert maths characters from a menu  -*-coding: iso-2022-7bit;-*-

;; Copyright (C) 2003, 2012  Free Software Foundation, Inc.

;; Author: Dave Love <fx@gnu.org>
;; Keywords: convenience

;; Version for Proof General modified by David Aspinall, 2007-8.
;; - Hooks added to insert tokenised versions of unicode characters.
;; - Added more characters to the menus.
;; - Define insertion functions following menu names (useful for keybindings)
;; maths-menu.el,v 12.1 2012/08/30 14:30:23 monnier Exp


;; This file is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 2, or (at your option)
;; any later version.

;; This file is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs; see the file COPYING.  If not, write to
;; the Free Software Foundation, Inc., 59 Temple Place - Suite 330,
;; Boston, MA 02111-1307, USA.

;;; Commentary:

;; Defines a minor mode which defines a menu bar item allowing a wide
;; range of maths/technical characters (roughly the LaTeX repertoire)
;; to be inserted into the buffer by selecting menu items.

;; Menu display only works properly under X with Gtk menus and if the
;; menu uses a font with a suitable repertoire.  (Lucid and Motif
;; toolkit menus can't display multilingual text.  I don't know about
;; MS Windows menus.)  It will work with tmm in tty mode iff the tty
;; displays Unicode.  The tmm version (via F10) is also useful under a
;; window system when the menus don't display the characters
;; correctly, but where the symbols have word syntax, tmm won't
;; provide an ASCII selector for them, which can be a pain to use
;; without a mouse.

;; See also the TeX and sgml Quail input modes.  These will probably
;; behave better if you can remember the input sequences.  For
;; instance, this minor mode won't give you the ability to insert into
;; the minibuffer via the menu, though presumably it could be added to
;; the minibuffer menu.



;;; Code:

(defvar maths-menu-filter-predicate (lambda (char) t)
  "Predicate function used to filter menu elements")

(defvar maths-menu-tokenise-insert #'insert
  "Function used to insert possibly formatted or escaped character.")

(defun maths-menu-build-menu (spec)
  (let ((map (make-sparse-keymap "Characters")))
    (dolist (pane spec)
      (let* ((name (pop pane))
	     (pane-map (make-sparse-keymap name)))
	(define-key-after map (vector (intern name)) (cons name pane-map))
	(dolist (elt pane)
	  (let ((fname (intern
			(concat "maths-menu-insert-"
				(replace-regexp-in-string " " "-" (cadr elt))))))
	    (fset fname
		  `(lambda ()
		     (interactive)
		     (funcall maths-menu-tokenise-insert ,(car elt))))
	    (define-key-after pane-map
	      (vector (intern (string (car elt)))) ; convenient unique symbol
	      (list 'menu-item
		    (format "%c  (%s)" (car elt) (cadr elt))
		    fname
		    :visible `(funcall maths-menu-filter-predicate ,(car elt))))))))
    map))

(defvar maths-menu-menu
  (maths-menu-build-menu
   '(("Logic"
      (?$A!D(B "and")
      (?$A!E(B "or")
      (?$,1x (B "for all")
      (?$,1x#(B "there exists")
      (?$,1x$(B "there does not exist")
      (?$,1yd(B "down tack")
      (?$,1ye(B "up tack"))
     ("Binops 1"
      (?,A1(B "plus-minus sign")
      (?$,1x3(B "minus-or-plus sign")
      (?,AW(B "multiplication sign")
      (?,Aw(B "division sign")
      (?$,1x2(B "minus sign")
      (?$,1x7(B "asterisk operator")
      (?$,1z&(B "star operator")
      (?$,2"+(B "white circle")
      (?$,1s"(B "bullet")
      (?,A7(B "middle dot")
      (?$,1xI(B "intersection")
      (?$,1xJ(B "union")
      (?$,1yN(B "multiset union")
      (?$,1yS(B "square cap")
      (?$,1yT(B "square cup")
      (?$,1xH(B "logical or")
      (?$,1xG(B "logical and")
      (?$,1x6(B "set minus")
      (?$,1x`(B "wreath product"))
     ("Binops 2"
      (?$,1z$(B "diamond operator")
      (?$,2!s(B "white up-pointing triangle")
      (?$,2!}(B "white down-pointing triangle")
      (?$,2"#(B "white left-pointing small triangle")
      (?$,2!y(B "white right-pointing small triangle")
      (?$,2"!(B "white left-pointing triangle")
      (?$,2!w(B "white right-pointing triangle")
      (?$,1yU(B "circled plus")
      (?$,1yV(B "circled minus")
      (?$,1yW(B "circled times")
      (?$,1yX(B "circled division slash")
      (?$,1yY(B "circled dot operator")
      (?$,2"O(B "large circle")
      (?$,1s (B "dagger")
      (?$,1s!(B "double dagger")
      (?$,1yt(B "normal subgroup of or equal to")
      (?$,1yu(B "contains as normal subgroup or equal to"))
     ("Relations 1"
      (?$,1y$(B "less-than or equal to")
      (?$,1y:(B "precedes")
      (?$,1y*(B "much less-than")
      (?$,1yB(B "subset of")
      (?$,1yF(B "subset of or equal to")
      (?$,1yO(B "square image of")
      (?$,1yQ(B "square image of or equal to")
      (?$,1x((B "element of")
      (?$,1x)(B "not an element of")
      (?$,1yb(B "right tack")
      (?$,1y%(B "greater-than or equal to")
      (?$,1y;(B "succeeds")
      (?$,1y=(B "succeeds or equal to")
      (?$,1y+(B "much greater-than")
      (?$,1yC(B "superset of")
      (?$,1yG(B "superset of or equal to")
      (?$,1yP(B "square original of")
      (?$,1yR(B "square original of or equal to")
      (?$,1x+(B "contains as member")
      (?$,1y!(B "identical to")
      (?$,1y"(B "not identical to") )
     ("Relations 2"
      (?$,1yc(B "left tack")
      (?$,1x\(B "tilde operator")
      (?$,1xc(B "asymptotically equal to")
      (?$,1xm(B "equivalent to")
      (?$,1xh(B "almost equal to")
      (?$,1xe(B "approximately equal to")
      (?$,1y (B "not equal to")
      (?$,1xp(B "approaches the limit")
      (?$,1x=(B "proportional to")
      (?$,1yg(B "models")
      (?$,1xC(B "divides")
      (?$,1xE(B "parallel to")
      (?$,1z((B "bowtie")
      (?$,1z((B "bowtie")
      (?$,1{#(B "smile")
      (?$,1{"(B "frown")
      (?$,1xy(B "estimates")
      (?$,1z_(B "z notation bag membership"))
     ("Arrows"
      (?$,1vp(B "leftwards arrow")
      (?$,1wP(B "leftwards double arrow")
      (?$,1vr(B "rightwards arrow")
      (?$,1wR(B "rightwards double arrow")
      (?$,1vt(B "left right arrow")
      (?$,1wT(B "left right double arrow")
      (?$,1w&(B "rightwards arrow from bar")
      (?$,1w)(B "leftwards arrow with hook")
      (?$,1w<(B "leftwards harpoon with barb upwards")
      (?$,1w=(B "leftwards harpoon with barb downwards")
      (?$,1wL(B "rightwards harpoon over leftwards harpoon")
      (?$,1w&(B "rightwards arrow from bar")
      (?$,1w*(B "rightwards arrow with hook")
      (?$,1w@(B "rightwards harpoon with barb upwards")
      (?$,1wA(B "rightwards harpoon with barb downwards")
      (?$,1v}(B "rightwards wave arrow")
      (?$,1vq(B "upwards arrow")
      (?$,1wQ(B "upwards double arrow")
      (?$,1vs(B "downwards arrow")
      (?$,1wS(B "downwards double arrow")
      (?$,1vu(B "up down arrow")
      (?$,1vw(B "north east arrow")
      (?$,1vx(B "south east arrow")
      (?$,1vy(B "south west arrow")
      (?$,1vv(B "north west arrow")
      (?$,1w[(B "rightwards triple arrow"))
     ("Long arrows"
      (?$,2'v(B "long rightwards arrow")
      (?$,2'w(B "long left right arrow")
      (?$,2'x(B "long left double arrow")
      (?$,2'y(B "long right double arrow")
      (?$,2'z(B "long left right double arrow")
      (?$,2'{(B "long left arrow from bar")
      (?$,2'|(B "long right arrow from bar")
      (?$,2'}(B "long left double arrow bar")
      (?$,2'~(B "long right double arrow from bar")
      (?$,2'(B "long rightwards squiggle arrow"))
     ("Symbols 1"
      (?$,1uu(B "alef symbol") ; don't use letter alef (avoid bidi confusion)
      (?$,1uO(B "planck constant over two pi")
      (?$,1 Q(B "latin small letter dotless i")
      (?$,1uS(B "script small l")
      (?$,1uX(B "script capital p")
      (?$,1u\(B "black-letter capital r")
      (?$,1uQ(B "black-letter capital i")
      (?$,1ug(B "inverted ohm sign")
      (?$,1s2(B "prime")
      (?$,1x%(B "empty set")
      (?$,1x'(B "nabla")
      (?$,1x:(B "square root")
      (?$,1x;(B "cube root")
      (?$,1x@(B "angle")
      (?,A,(B "not sign")
      (?$,2#o(B "music sharp sign")
      (?$,1x"(B "partial differential")
      (?$,1x>(B "infinity") )
     ("Symbols 2"
      (?$,2!a(B "white square")
      (?$,2"'(B "white diamond")
      (?$,2!u(B "white up-pointing small triangle")
      (?$,1x1(B "n-ary summation")
      (?$,1x/(B "n-ary product")
      (?$,1x0(B "n-ary coproduct")
      (?$,1xK(B "integral")
      (?$,1xN(B "contour integral")
      (?$,1z"(B "n-ary intersection")
      (?$,1z#(B "n-ary union")
      (?$,1z!(B "n-ary logical or")
      (?$,1z (B "n-ary logical and")
      (?$,1uU(B "double-struck capital n")
      (?$,1uY(B "double-struck capital p")
      (?$,1uZ(B "double-struck capital q")
      (?$,1u](B "double-struck capital r")
      (?$,1ud(B "double-struck capital z")
      (?$,1uP(B "script capital i")
      (?$,1![(B "latin small letter lambda with stroke")
      (?$,1xT(B "therefore")
      (?$,1s&(B "horizontal ellipsis")
      (?$,1zO(B "midline horizontal ellipsis")
      (?$,1zN(B "vertical ellipsis")
      (?$,1zQ(B "down right diagonal ellipsis")
      (?$,1zP(B "up right diagonal ellipsis")
      (?$,2,!(B "z notation spot")
      (?$,2,"(B "z notation type colon"))
     ("Delimiters"
      (?\$,1zj(B "left floor")
      (?\$,1zh(B "left ceiling")
      (?\$,1{)(B "left-pointing angle bracket")
      (?\$,1zk(B "right floor")
      (?\$,1zi(B "right ceiling")
      (?\$,1{*(B "right-pointing angle bracket")
      (?\$,2=Z(B "left white square bracket")
      (?\$,2=[(B "right white square bracket")
      (?\$,2=J(B "left double angle bracket")
      (?\$,2=K(B "right double angle bracket")
      (?\$,2,'(B "z notation left image bracket")
      (?\$,2,((B "z notation right image bracket")
      (?\$,2,)(B "z notation left binding bracket")
      (?\$,2,*(B "z notation right binding bracket"))
     ("Greek LC"
      (?$,1'1(B "alpha")
      (?$,1'2(B "beta")
      (?$,1'3(B "gamma")
      (?$,1'4(B "delta")
      (?$,1'5(B "epsilon")
      (?$,1'6(B "zeta")
      (?$,1'7(B "eta")
      (?$,1'8(B "theta")
      (?$,1'Q(B "theta symbol")
      (?$,1'9(B "iota")
      (?$,1':(B "kappa")
      (?$,1';(B "lamda")
      (?$,1'<(B "mu")
      (?$,1'=(B "nu")
      (?$,1'>(B "xi")
      (?$,1'@(B "pi")
      (?$,1'V(B "pi symbol")
      (?$,1'A(B "rho")
      (?$,1'q(B "rho symbol")
      (?$,1'C(B "sigma")
      (?$,1'B(B "final sigma")
      (?$,1'D(B "tau")
      (?$,1'E(B "upsilon")
      (?$,1'F(B "phi")
      (?$,1'U(B "phi symbol")
      (?$,1'G(B "chi")
      (?$,1'H(B "psi")
      (?$,1'I(B "omega"))
     ("Greek UC"
      (?$,1&s(B "Gamma")
      (?$,1&t(B "Delta")
      (?$,1&x(B "Theta")
      (?$,1&{(B "Lamda")
      (?$,1&~(B "Xi")
      (?$,1' (B "Pi")
      (?$,1'#(B "Sigma")
      (?$,1'%(B "Upsilon")
      (?$,1'&(B "Phi")
      (?$,1'((B "Psi")
      (?$,1')(B "Omega"))
     ("Sub/super"
      (?$,1s}(B "superscript left parenthesis")
      (?$,1s~(B "superscript right parenthesis")
      (?$,1sz(B "superscript plus sign")
      (?$,1s{(B "superscript minus")
      (?$,1sp(B "superscript zero")
      (?,A9(B "superscript one")
      (?,A2(B "superscript two")
      (?,A3(B "superscript three")
      (?$,1st(B "superscript four")
      (?$,1su(B "superscript five")
      (?$,1sv(B "superscript six")
      (?$,1sw(B "superscript seven")
      (?$,1sx(B "superscript eight")
      (?$,1sy(B "superscript nine")
      (?$,1t-(B "subscript left parenthesis")
      (?$,1t.(B "subscript right parenthesis")
      (?$,1t*(B "subscript plus sign")
      (?$,1t+(B "subscript minus")
      (?$,1t (B "subscript zero")
      (?$,1t!(B "subscript one")
      (?$,1t"(B "subscript two")
      (?$,1t#(B "subscript three")
      (?$,1t$(B "subscript four")
      (?$,1t%(B "subscript five")
      (?$,1t&(B "subscript six")
      (?$,1t'(B "subscript seven")
      (?$,1t((B "subscript eight")
      (?$,1t)(B "subscript nine")))))

(defvar maths-menu-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map [menu-bar maths]
      `(menu-item "Maths" ,maths-menu-menu
		  :help "Menu of maths characters to insert"))
    map))

;;;###autoload
(define-minor-mode maths-menu-mode
  "Install a menu for entering mathematical characters.
Uses window system menus only when they can display multilingual text.
Otherwise the menu-bar item activates the text-mode menu system.
This mode is only useful with a font which can display the maths repertoire."
  nil nil maths-menu-mode-map)

(provide 'maths-menu)
;;; maths-menu.el ends here
