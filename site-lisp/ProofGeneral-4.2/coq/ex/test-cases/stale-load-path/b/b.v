(* This file depends on ../a/Le.v *)

Require Le.

(* The next print should work. *)
Print Le.a.

(* The next print should not work. *)
Print Le.le_refl.


(*** Local Variables: ***)
(*** coq-load-path: ("../a") ***)
(*** End: ***)
