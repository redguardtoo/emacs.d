(* Some scripting tests for modules.  Pierre Courtieu.  *)
Module Type O1.
  Parameter A:Set.
  Parameter B:Set.
End O1.


Module R:O1.
  Definition A:=nat.
  Definition B:=bool.
End R.

Module R2: O1 with 
  Definition  A:=nat.
  Definition A:=nat.
  Definition B:=bool.
End R2.

Module R4.
  Module R3: O1 with Definition  A:=nat :=R2.
End R4.




Module M.

  Module Type SIG.
    Parameter T:Set.
    Parameter x:T.
  End SIG.

  Module Type SIG'.
    Parameter T:Set.
    Parameter x:T.
  End SIG'.

  Lemma toto : O=O.
    Definition t:=nat.
    trivial.
  Save.

  Module N:SIG.
    Definition T:=nat.
    Definition x:=O.
  End N.
  Module O:=N.
End M.

Import M.
Print t.


Definition t:O=O.
  trivial.
Save.


Section toto.
  Print M.
End toto.

Module N:=M.


Module Type typ.
  Parameter T:Set.
  Parameter a:T.
End typ.



Module Type N'.
  Module Type M'.
    Declare Module K:N.SIG.
  End M'.
(*   Declare Module N''. *)
  Definition T:=nat.
  Definition x:=O.
(*   End N''. *)
  
  Declare Module N':M.SIG. (* no interactive def started *)
  Declare Module N''' :M.SIG. (* no interactive def started *)
End N'.



Lemma titi : O=O.
  trivial.
  Module Type K:=N'.
  Module N''':=M.
Save.
