(*
    Example uses of Unicode Tokens symbols in Coq.
    See README.
    Trac this at http://proofgeneral.inf.ed.ac.uk/trac/ticket/313

    Pierre Courtieu, David Aspinall.

    Turn on with Proof-General → Quick Options → Display → Unicode Tokens

    example-tokens.v,v 11.0 2010/10/10 22:56:58 da Exp
*)

Module ExampleTokens.

Fixpoint toto (x:nat) {struct x} : nat := (* n a t  should appear as |N *)
  match x with
    | O => O        (* double arrow here *)
    | S y => toto y (* double arrow here *)
  end.

Lemma titi : forall x:nat,x=x. (* symbolique for-all and n at *)
Admitted. 

(* X-Symbol: this previously appeared as foo'a'1_B_3 where a and B are greek.
   Unicode Tokens: this doesn't happen because the regexp used to match
   is matching on sequences limited by word.
   Syntax table matters here: try  (modify-syntax-entry ?\' ".")
                                   (modify-syntax-entry ?\_ ".")
 *)
Variable foo'alpha'1__beta__3 : Set.  
Fixpoint pow (n m:nat) {struct n} : nat :=
  match n with
	 | O => 0
	 | S p => m * pow p m
  end.

Variable a b : nat.

Notation "a,{b}" := (a - b)
  (at level 1, no associativity).

Notation "a^^b" := (pow a b)
  (at level 1, no associativity).

Notation "a^{b}" := (pow a b)
  (at level 1, no associativity, only parsing).


Variable delta:nat.

(* greek delta with a sub 1 and the same with super 1 *)
Definition delta__1 := 0. 
(*Definition delta__2 := delta^^1. *)
(* Definition delta__3:= delta__2^{delta}. *)

Parameter x:nat.

(* x with a+b subscripted and then superscripted *)
(*Definition x_a_b' := x^{a+b}.  *)
(*Definition x_a_b := x,{a+b}. *)
(*Definition x_a_b'' := x,{a+b}^{a*b}.*)

(* no greek letter should appear on this next line! *)
Variable philosophi   : Set.

(* same here *)
Variable aalpha alphaa : Set.


(* _a where a is greek *)
Variable _alpha : Set.

(* a_ where a is greek *)
Variable alpha_ : Set.

Lemma gamma__neqn : forall n__i:nat, n__i=n__i.
Abort All.

(* Tests of things that shouldn't be 
should be unicode characters: alpha lhd rhd lambda forall exists exists 
shouldn't be altered: exist foral 
*)

End ExampleTokens.