#use"TacticRecording/main.ml";;
#use "TacticRecording/biolayout.ml";;

pg_mode_off ();;

g `x = x /\ y = y /\ z = z`;;
e (CONJ_TAC);;
e (REFL_TAC);;
e (CONJ_TAC);;
e (REFL_TAC);;
e (REFL_TAC);;
let th = top_thm ();;

g `(!x. x = x) /\ (!y.y = y) /\ (!z.z = z)`;;
e (REPEAT CONJ_TAC THEN GEN_TAC);;
e (REFL_TAC);;
e (REFL_TAC);;
e (REFL_TAC);;
let th = top_thm ();;

g `(!x. x = x) /\ (!y.y = y) /\ (!z.z = z)`;;
e (CONJ_TAC);;
e (GEN_TAC);;
e (REFL_TAC);;
e (CONJ_TAC);;
e (GEN_TAC);;
e (REFL_TAC);;
e (GEN_TAC);;
e (REFL_TAC);;
let th = top_thm ();;

g `(!x. x = x) /\ (!y.y = y) /\ (!z.z = z)`;;
e (REPEAT CONJ_TAC);;
e (GEN_TAC);;
e (REFL_TAC);;
e (GEN_TAC);;
e (REFL_TAC);;
e (GEN_TAC);;
e (REFL_TAC);;
let th = top_thm ();;

g `(!x. x = x) /\ (!y.y = y) /\ (!z.z = z)`;;
e (REPEAT CONJ_TAC THEN GEN_TAC THEN REFL_TAC);;
let th = top_thm ();;

print_executed_proof true;;
print_flat_proof true;;
print_thenl_proof ();;
print_packaged_proof ();;
print_gv_proof ();;

g `(y:A) = z ==> (x:A) = x /\ y = y /\ z = z`;;
e (STRIP_TAC);;
e (UNDISCH_TAC `(y:A) = z`);;
e (DISCH_TAC);;
e (CONJ_TAC);;
e (REFL_TAC);;
e (CONJ_TAC);;
e (REFL_TAC);;
e (REFL_TAC);;




