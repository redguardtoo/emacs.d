(* A sample tarski theorem proof, for f: A -> A. 
   Syntax is for coq v8. *)

Parameter A : Set.
Variable R : A -> A -> Prop.
Variable Eq : A -> A -> Prop.

Axiom Assym : forall x y : A, R x y -> R y x -> Eq x y.
Axiom Trans : forall x y z : A, R x y -> R y z -> R x z.

Variable f : A -> A.
Axiom Incr : forall x y : A, R x y -> R (f x) (f y).

Variable M : A.
Hypothesis Up : forall x : A, R x (f x) -> R x M.
Hypothesis Least : forall x : A, (forall y : A, R y (f y) -> R y x) -> R M x.

Hint Resolve Up Assym Incr Least Incr Up Trans : db.

Theorem Tarski_lemma : Eq M (f M).
(* We can prove the theorem in one line: *)
(*   eauto 15 with db.  *)
(* But we rather use basic tactics in this sample file: *)
  cut (R M (f M)).
  intro.
  apply Assym; trivial.
  apply Up.
  apply Incr; trivial.
  apply Least.
  intros.
  apply Trans with (f y); trivial.
  apply Incr.
  apply Up; trivial.
Qed.
