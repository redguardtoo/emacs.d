#use "hol.ml";;
needs "Examples/prime.ml";;

#use "TacticRecording/main.ml";;


let egcd = define
 `egcd(m,n) = if m = 0 then n 
              else if n = 0 then m
              else if m <= n then egcd(m,n - m)
              else egcd(m - n,n)`;;

let egcd = theorem_wrap "egcd" egcd;;
let DIVIDES_0 =  theorem_wrap "DIVIDES_0" DIVIDES_0;;
let WF_INDUCT_TAC = term_tactic_wrap "WF_INDUCT_TAC" WF_INDUCT_TAC;;

g `!m n d. d divides egcd(m,n) <=> d divides m /\ d divides n`;;
e (GEN_TAC THEN GEN_TAC THEN WF_INDUCT_TAC `m + n` THEN
   GEN_TAC THEN ONCE_REWRITE_TAC[egcd] THEN
   ASM_CASES_TAC `m = 0` THEN ASM_REWRITE_TAC[DIVIDES_0] THEN
   ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[DIVIDES_0] THEN 
   COND_CASES_TAC);;
top_goal ();;

print_executed_proof ();;
print_flat_proof ();;
print_thenl_proof ();;
print_optimal_proof ();;
is_empty [23];;
not true or not true;;

let EGCD_INVARIANT = prove
 (`!m n d. d divides egcd(m,n) <=> d divides m /\ d divides n`,
  GEN_TAC THEN GEN_TAC THEN WF_INDUCT_TAC `m + n` THEN
  GEN_TAC THEN ONCE_REWRITE_TAC[egcd] THEN
  ASM_CASES_TAC `m = 0` THEN ASM_REWRITE_TAC[DIVIDES_0] THEN
  ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[DIVIDES_0] THEN 
  COND_CASES_TAC THEN
  (W(fun (asl,w) -> FIRST_X_ASSUM(fun th ->
    MP_TAC(PART_MATCH (lhs o snd o dest_forall o rand) th (lhand w)))) THEN
   ANTS_TAC THENL [REPEAT(POP_ASSUM MP_TAC) THEN ARITH_TAC; ALL_TAC]) THEN
  ASM_MESON_TAC[DIVIDES_SUB; DIVIDES_ADD; SUB_ADD; LE_CASES]);;
  


