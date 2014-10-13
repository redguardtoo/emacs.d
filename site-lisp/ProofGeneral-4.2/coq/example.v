(*
    Example proof script for Coq Proof General.

    example.v,v 11.0 2010/10/10 22:56:58 da Exp
*)

Module Example.

Goal forall (A B:Prop),(A /\ B) -> (B /\ A). 
  intros A B.
  intros H.
  elim H.
  split.
  assumption.
  assumption.
Save and_comms.

End Example.
