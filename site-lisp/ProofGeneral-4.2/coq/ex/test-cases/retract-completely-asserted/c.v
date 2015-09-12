
Require Import a.
Require Import b.

(* b.a hides a.a, therefore the partial name "a" refers to b.a *)
Print a.

(* a.a is available under its longer name *)
Print a.a.