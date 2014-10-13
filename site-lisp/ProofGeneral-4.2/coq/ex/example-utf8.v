(* -*- coding: utf-8; -*- *)

(* utf8 notations: You can (re)use the version here, 
   or a compiled version distributed with Coq IDE: 
    Add LoadPath "/usr/lib/coq/ide". 
    Require Import utf8.
*)
Load "utf8".

(* Printing of unicode notation, in *goals* *)
Lemma test : ∀ A:Prop, A -> A.
auto.
Qed.

(* Parsing of unicode notation here, printing in *goals* *) 
Lemma test2 : ∀ A:Prop, A → A.
intro.
intro.
auto.
Qed.

(* Printing of unicode notation, in *response* *)
Check (fun (X:Set)(x:X) => x).

(* Parsing of unicode notation here, printing in *response* *)
Check (∀A, A→A).