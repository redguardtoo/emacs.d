(*
    Example proof script for Lego Proof General.
 
    example.l,v 12.0 2011/10/13 10:54:50 da Exp
*)

Module example Import lib_logic;

Goal {A,B:Prop}(A /\ B) -> (B /\ A);
intros;
Refine H;
intros;
andI;
Immed;
Save and_comms;
