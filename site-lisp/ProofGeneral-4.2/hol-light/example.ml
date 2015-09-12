(*
    Example proof script for HOL Proof General.

    example.ml,v 12.2 2012/02/08 18:29:13 da Exp
*)    

g `A /\ B ==> B /\ A`;;
e DISCH_TAC;;
e CONJ_TAC;;
e (ASM_SIMP_TAC[]);;
e (ASM_SIMP_TAC[]);;
let and_comms = top_thm();;

g `A /\ B ==> B /\ A`;;
e DISCH_TAC;;
e CONJ_TAC;;
e (ASM_SIMP_TAC[]);;
e (ASM_SIMP_TAC[]);;
let and_comms2 = top_thm();;
