(* This file depends on Coq.Arith.Le from the standard library. *)

Require Le.

(* The next print should work. *)
Print Le.le_refl.

(* The next print should not work. *)
Print Le.a.
