Require Import Arith.
Require mult1.
Definition bar:bool := if le_lt_dec foo 0 then true else false.


