(* An example of customization file for the hightlight of the Coq Mode *)

(*Supposing you .emacs contains the following lines:

(load-file "<proofgeneral-home>/generic/proof-site.el")
(load-file "<location>/pg-ssr.el")

And that the file my-tacs.el contains for instance:
---

(defcustom coq-user-tactics-db
   '(("nat_congr" "ncongr"  "nat_congr" t "nat_congr")
     ("nat_norm" "nnorm"  "nat_norm" t "nat_norm")
     ("bool_congr" "bcongr"  "bool_congr" t "bool_congr")
     ("prop_congr" "prcongr"  "prop_congr" t "prop_congr")
     ("move" "m"  "move" t "move")
     ("pose" "po"  "pose # := #" t "pose")
     ("set" "set"  "set # := #" t "set")
     ("have" "hv" "have # : #" t "have") 
     ("congr" "con" "congr #" t "congr")
     ("wlog" "wlog" "wlog : / #" t "wlog")
     ("without loss" "wilog" "without loss #" t "without loss")
     ("unlock" "unlock" "unlock #" t "unlock")
     ("suffices" "suffices" "suffices # : #" t "suffices")
     ("suff" "suff" "suff # : #" t "suff")
) 
   "Extended list of tactics, includings ssr and user defined ones")


(defcustom coq-user-commands-db
  '(("Prenex Implicits" "pi" "Prenex Implicits #" t "Prenex\\s-+Implicits")
    ("Hint View for" "hv" "Hint View for #" t "Hint\\s-+View\\s-+for")
    ("inside" "ins" nil f "inside")
    ("outside" "outs" nil f "outside")
)
   "Extended list of commands, includings ssr and user defined ones")

(defcustom coq-user-tacticals-db
  '(("last" "lst" nil t "last"))
  "Extended list of tacticals, includings ssr and user defined ones")

(defcustom coq-user-reserved-db
  '("is" "nosimpl" "of")
  "Extended list of keywords, includings ssr and user defined ones")

(defcustom coq-user-solve-tactics-db
  '(("done" nil "done" nil "done")
    )
   "Extended list of closing tactic(al)s, includings ssr and user defined ones")
---
Below is a sample script file coloured by this customised mode:

*)



Require Import ssreflect.
Require Import ssrbool.
Require Import ssrnat.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


Inductive mylist (A : Type) : Type := mynil | mycons of A & mylist A.

(***************** The stack******************)

Goal forall A B : Prop, A -> (A -> B) -> B.
Proof. move=> A B Ha; exact. Qed.

(***************** Bookkeeping **************)

Lemma my_mulnI : forall x y, mult x y = muln x y.
Proof. elim=> // m Hrec n /=; congr addn; done. Qed.


(* Warning : corecion bool >-> Prop *)
Lemma demo_bool : forall x y z: bool,
  x && y -> z -> x && y && z.
Proof. by move=> x y z -> ->. Qed.

(* com + assoc *)
Lemma my_addnCA : forall m n p, m + (n + p) = n + (m + p).
Proof.  
by move=> m n; elim: m => [|m Hrec] p; rewrite ?addSnnS -?addnS. Qed.

(*** Rotation of subgoals *)
Inductive test : nat -> Prop :=
  C1 : forall n, test n | C2 : forall n, test n |
  C3 : forall n, test n | C4 : forall n, test n.
Goal forall n, test n -> True.
move=> n t; case: t; last 1  [move=> k| move=> l]; last first.
Admitted.

(*** Selection of subgoals *)
Goal forall n, test n -> True.
move=> n t; case E: t; first 1 last.
Admitted.


(*** Forward chaining *)
Lemma demo_fwd : forall x y : nat, x = y.
Proof.
move=> x y.
 suff [H1 H2] : (x, y) = (x * 1, y + 0).
Admitted.

Lemma demo_fwd2 : forall x y : nat, x = y.
Proof.
move=> x y.
  wlog : x  / x <= y.
Admitted.



Lemma rwtest1 : let x := 3 in x * 2 = 6.
Proof. move=> x. rewrite /x //=. Qed.
(* => unfold + simpl *)

Lemma rwtest2 : forall x, 0 * x =  0.
Proof. move=> x. rewrite -[0 * x]/0 //. Qed.
(* => conversion *)

Goal (forall t u, t + u = u + t) -> forall x y, x + y = y + x.
Proof. by move=> H x y; rewrite (*[x + _ ]H *) [_ + y]H. Qed.
(* => with patterns *)

Goal (forall t u, t + u = u + t) -> 
  forall x y, x + y + (y + x) = y + x.
move=> H x y;  rewrite {2}(H y).
Admitted.
(* => occurrence selection *)


