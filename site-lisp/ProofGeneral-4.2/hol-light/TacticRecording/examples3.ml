#use"hol.ml";;
needs "Library/products.ml";;

#use "TacticRecording/main.ml";;

prioritize_real();;

AIM: CONT_COMPOSE (Library/analysis.ml)
- used by John in his Proof Style paper


(* ** LEMMA1 from HOL Light's 100/arithmetic_geometric_mean.ml ** *)

let LEMMA_1 = prove
 (`!x n. x pow (n + 1) - (&n + &1) * x + &n =
         (x - &1) pow 2 * sum(1..n) (\k. &k * x pow (n - k))`,
  CONV_TAC(ONCE_DEPTH_CONV SYM_CONV) THEN GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH_EQ; ADD_CLAUSES] THENL
   [REAL_ARITH_TAC; REWRITE_TAC[ARITH_RULE `1 <= SUC n`]] THEN
  SIMP_TAC[ARITH_RULE `k <= n ==> SUC n - k = SUC(n - k)`; SUB_REFL] THEN
  REWRITE_TAC[real_pow; REAL_MUL_RID] THEN
  REWRITE_TAC[REAL_ARITH `k * x * x pow n = (k * x pow n) * x`] THEN
  ASM_REWRITE_TAC[SUM_RMUL; REAL_MUL_ASSOC; REAL_ADD_LDISTRIB] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_SUC; REAL_POW_ADD] THEN REAL_ARITH_TAC);;

let LEMMA_1 = prove
 (`!x n. x pow (n + 1) - (&n + &1) * x + &n =
         (x - &1) pow 2 * sum(1..n) (\k. &k * x pow (n - k))`,
  CONV_TAC(ONCE_DEPTH_CONV SYM_CONV) THEN GEN_TAC THEN
  HILABEL "induction"
         (INDUCT_TAC THEN
          REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH_EQ; ADD_CLAUSES] THENL
   [HILABEL "base case" REAL_ARITH_TAC; ALL_TAC] THEN
  HILABEL "step case" (REWRITE_TAC[ARITH_RULE `1 <= SUC n`] THEN
  SIMP_TAC[ARITH_RULE `k <= n ==> SUC n - k = SUC(n - k)`; SUB_REFL] THEN
  REWRITE_TAC[real_pow; REAL_MUL_RID] THEN
  REWRITE_TAC[REAL_ARITH `k * x * x pow n = (k * x pow n) * x`] THEN
  ASM_REWRITE_TAC[SUM_RMUL; REAL_MUL_ASSOC; REAL_ADD_LDISTRIB] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_SUC; REAL_POW_ADD] THEN REAL_ARITH_TAC)));;

let LEMMA_1 = theorem_wrap "LEMMA_1" LEMMA_1;;

top_thm ();;
print_executed_proof true;;
print_flat_proof true;;
print_packaged_proof ();;
print_thenl_proof ();;
print_gv_proof ();;

let gtr = !the_goal_tree;;
let h = gtree_to_hiproof gtr;;
let h' = (trivsimp_hiproof o dethen_hiproof) h;;

g `!x n. x pow (n + 1) - (&n + &1) * x + &n =
         (x - &1) pow 2 * sum(1..n) (\k. &k * x pow (n - k))`;;
e (CONV_TAC (ONCE_DEPTH_CONV SYM_CONV));;
e (GEN_TAC);;
e (INDUCT_TAC);;
(* *** Subgoal 1 *** *)
e (REWRITE_TAC [SUM_CLAUSES_NUMSEG;ARITH_EQ;ADD_CLAUSES]);;
e (REAL_ARITH_TAC);;
(* *** Subgoal 2 *** *)
e (REWRITE_TAC [SUM_CLAUSES_NUMSEG;ARITH_EQ;ADD_CLAUSES]);;
e (REWRITE_TAC [ARITH_RULE `1 <= SUC n`]);;
e (SIMP_TAC [ARITH_RULE `k <= n ==> SUC n - k = SUC (n - k)`; SUB_REFL]);;
e (REWRITE_TAC [real_pow;REAL_MUL_RID]);;
e (REWRITE_TAC [REAL_ARITH `k * x * x pow n = (k * x pow n) * x`]);;
e (ASM_REWRITE_TAC [SUM_RMUL;REAL_MUL_ASSOC;REAL_ADD_LDISTRIB]);;
e (REWRITE_TAC [GSYM REAL_OF_NUM_SUC; REAL_POW_ADD]);;
e (REAL_ARITH_TAC);;

print_executed_proof true;;
print_packaged_proof ();;
print_thenl_proof ();;

(* LEMMA 2 *)

let LEMMA_2 = prove
 (`!n x. &0 <= x ==> &0 <= x pow (n + 1) - (&n + &1) * x + &n`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LEMMA_1] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POW_2; REAL_LE_SQUARE] THEN
  MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN
  ASM_SIMP_TAC[REAL_LE_MUL; REAL_POS; REAL_POW_LE]);;

let LEMMA_2 = theorem_wrap "LEMMA_2" LEMMA_2;;

print_executed_proof true;;
print_flat_proof true;;
print_packaged_proof ();;
print_gv_proof ();;

g `!n x. &0 <= x ==> &0 <= x pow (n + 1) - (&n + &1) * x + &n`;;

(* LEMMA 3 *)

let LEMMA_3 = prove
 (`!n x. 1 <= n /\ (!i. 1 <= i /\ i <= n + 1 ==> &0 <= x i)
         ==> x(n + 1) * (sum(1..n) x / &n) pow n
                <= (sum(1..n+1) x / (&n + &1)) pow (n + 1)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `a = sum(1..n+1) x / (&n + &1)` THEN
  ABBREV_TAC `b = sum(1..n) x / &n` THEN
  SUBGOAL_THEN `x(n + 1) = (&n + &1) * a - &n * b` SUBST1_TAC THENL
   [MAP_EVERY EXPAND_TAC ["a"; "b"] THEN
    ASM_SIMP_TAC[REAL_DIV_LMUL; REAL_OF_NUM_EQ; LE_1;
                 REAL_ARITH `~(&n + &1 = &0)`] THEN
    SIMP_TAC[SUM_ADD_SPLIT; ARITH_RULE `1 <= n + 1`; SUM_SING_NUMSEG] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= a /\ &0 <= b` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["a"; "b"] THEN CONJ_TAC THEN
    MATCH_MP_TAC REAL_LE_DIV THEN
    (CONJ_TAC THENL [MATCH_MP_TAC SUM_POS_LE_NUMSEG; REAL_ARITH_TAC]) THEN
    ASM_SIMP_TAC[ARITH_RULE `p <= n ==> p <= n + 1`];
    ALL_TAC] THEN
  ASM_CASES_TAC `b = &0` THEN
  ASM_SIMP_TAC[REAL_POW_ZERO; LE_1; REAL_MUL_RZERO; REAL_POW_LE] THEN
  MP_TAC(ISPECL [`n:num`; `a / b`] LEMMA_2) THEN ASM_SIMP_TAC[REAL_LE_DIV] THEN
  REWRITE_TAC[REAL_ARITH `&0 <= x - a + b <=> a - b <= x`; REAL_POW_DIV] THEN
  SUBGOAL_THEN `&0 < b` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_POW_LT] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[REAL_POW_ADD] THEN UNDISCH_TAC `~(b = &0)` THEN
  CONV_TAC REAL_FIELD);;

let LEMMA_3 = theorem_wrap "LEMMA_3" LEMMA_3;;

print_executed_proof true;;
print_flat_proof true;;
print_thenl_proof ();;
print_packaged_proof ();;
print_gv_proof ();;

g `!n x. 1 <= n /\ (!i. 1 <= i /\ i <= n + 1 ==> &0 <= x i)
         ==> x(n + 1) * (sum(1..n) x / &n) pow n
                <= (sum(1..n+1) x / (&n + &1)) pow (n + 1)`;;

print_flat_proof true;;
e (STRIP_TAC);;
e (STRIP_TAC);;
e (STRIP_TAC);;
e (ABBREV_TAC `a = sum (1..n + 1) x / (&n + &1)`);;
e (ABBREV_TAC `b = sum (1..n) x / &n`);;
e (SUBGOAL_THEN `x (n + 1) = (&n + &1) * a - &n * b` SUBST1_TAC);;
(* *** Subgoal 1 *** *)
e (EXPAND_TAC "a");;
e (EXPAND_TAC "b");;
e (ASM_SIMP_TAC [REAL_DIV_LMUL; REAL_OF_NUM_EQ; LE_1; REAL_ARITH `~(&n + &1 = &0)`]);;
e (SIMP_TAC [SUM_ADD_SPLIT; ARITH_RULE `1 <= n + 1`; SUM_SING_NUMSEG]);;
e (REAL_ARITH_TAC);;
(* *** Subgoal 2 *** *)
e (SUBGOAL_THEN `&0 <= a /\ &0 <= b` STRIP_ASSUME_TAC);;
(* *** Subgoal 2.1 *** *)
e (EXPAND_TAC "a");;
e (EXPAND_TAC "b");;
e (CONJ_TAC);;
(* *** Subgoal 2.1.1 *** *)
e (MATCH_MP_TAC REAL_LE_DIV);;
e (CONJ_TAC);;
(* *** Subgoal 2.1.1.1 *** *)
e (MATCH_MP_TAC SUM_POS_LE_NUMSEG);;
e (ASM_SIMP_TAC [ARITH_RULE `p <= n ==> p <= n + 1`]);;
(* *** Subgoal 2.1.1.2 *** *)
e (REAL_ARITH_TAC);;
(* *** Subgoal 2.1.2 *** *)
e (MATCH_MP_TAC REAL_LE_DIV);;
e (CONJ_TAC);;
(* *** Subgoal 2.1.2.1 *** *)
e (MATCH_MP_TAC SUM_POS_LE_NUMSEG);;
e (ASM_SIMP_TAC [ARITH_RULE `p <= n ==> p <= n + 1`]);;
(* *** Subgoal 2.1.2.2 *** *)
e (REAL_ARITH_TAC);;
(* *** Subgoal 2.2 *** *)
e (ASM_CASES_TAC `b = &0`);;
(* *** Subgoal 2.2.1 *** *)
e (ASM_SIMP_TAC [REAL_POW_ZERO;LE_1;REAL_MUL_RZERO;REAL_POW_LE]);;
(* *** Subgoal 2.2.2 *** *)
e (ASM_SIMP_TAC [REAL_POW_ZERO;LE_1;REAL_MUL_RZERO;REAL_POW_LE]);;
e (MP_TAC (ISPECL [`n`;`a / b`] LEMMA_2));;
e (ASM_SIMP_TAC [REAL_LE_DIV]);;
e (REWRITE_TAC [REAL_ARITH `&0 <= x - a + b <=> a - b <= x`; REAL_POW_DIV]);;
e (SUBGOAL_THEN `&0 < b` ASSUME_TAC);;
(* *** Subgoal 2.2.2.1 *** *)
e (ASM_REAL_ARITH_TAC);;
(* *** Subgoal 2.2.2.2 *** *)
e (ASM_SIMP_TAC [REAL_LE_RDIV_EQ;REAL_POW_LT]);;
e (MATCH_MP_TAC EQ_IMP);;
e (AP_THM_TAC);;
e (AP_TERM_TAC);;
e (REWRITE_TAC [REAL_POW_ADD]);;
e (UNDISCH_TAC `~(b = &0)`);;
e (CONV_TAC REAL_FIELD);;

(* AGM *)

let AGM = prove
 (`!n a. 1 <= n /\ (!i. 1 <= i /\ i <= n ==> &0 <= a(i))
         ==> product(1..n) a <= (sum(1..n) a / &n) pow n`,
  INDUCT_TAC THEN REWRITE_TAC[ARITH; PRODUCT_CLAUSES_NUMSEG] THEN
  REWRITE_TAC[ARITH_RULE `1 <= SUC n`] THEN X_GEN_TAC `x:num->real` THEN
  ASM_CASES_TAC `n = 0` THENL
   [ASM_REWRITE_TAC[PRODUCT_CLAUSES_NUMSEG; ARITH; SUM_SING_NUMSEG] THEN
    REAL_ARITH_TAC;
    REWRITE_TAC[ADD1] THEN STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN     
    EXISTS_TAC `x(n + 1) * (sum(1..n) x / &n) pow n` THEN
    ASM_SIMP_TAC[LEMMA_3; GSYM REAL_OF_NUM_ADD; LE_1;
                 ARITH_RULE `i <= n ==> i <= n + 1`] THEN
    GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_SIMP_TAC[LE_REFL; LE_1; ARITH_RULE `i <= n ==> i <= n + 1`]]);;

g `!n a. 1 <= n /\ (!i. 1 <= i /\ i <= n ==> &0 <= a(i))
         ==> product(1..n) a <= (sum(1..n) a / &n) pow n`;;
e (INDUCT_TAC);;
(* *** Subgoal 1 *** *)
e (REWRITE_TAC [ARITH;PRODUCT_CLAUSES_NUMSEG]);;
(* *** Subgoal 2 *** *)
e (REWRITE_TAC [ARITH;PRODUCT_CLAUSES_NUMSEG]);;
e (REWRITE_TAC [ARITH_RULE `1 <= SUC n`]);;
e (X_GEN_TAC `x:num->real`);;
e (ASM_CASES_TAC `n = 0`);;
(* *** Subgoal 2.1 *** *)
e (ASM_REWRITE_TAC [PRODUCT_CLAUSES_NUMSEG;ARITH;SUM_SING_NUMSEG]);;
e (REAL_ARITH_TAC);;
(* *** Subgoal 2.2 *** *)
e (REWRITE_TAC [ADD1]);;
e (STRIP_TAC);;
e (MATCH_MP_TAC REAL_LE_TRANS);;
e (EXISTS_TAC `x (n + 1) * (sum (1..n) x / &n) pow n`);;
e (ASM_SIMP_TAC [LEMMA_3; GSYM REAL_OF_NUM_ADD; LE_1; ARITH_RULE `i <= n ==> i <= n + 1`]);;
e (GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM]);;
e (MATCH_MP_TAC REAL_LE_RMUL);;
e (ASM_SIMP_TAC [LE_REFL; LE_1; ARITH_RULE `i <= n ==> i <= n + 1`]);;

g `!n a. 1 <= n /\ (!i. 1 <= i /\ i <= n ==> &0 <= a(i))
         ==> product(1..n) a <= (sum(1..n) a / &n) pow n`;;
e (INDUCT_TAC THEN REWRITE_TAC [ARITH;PRODUCT_CLAUSES_NUMSEG] THEN REWRITE_TAC [ARITH_RULE `1 <= SUC n`] THEN X_GEN_TAC `x:num->real` THEN ASM_CASES_TAC `n = 0` THENL [ASM_REWRITE_TAC [PRODUCT_CLAUSES_NUMSEG;ARITH;SUM_SING_NUMSEG] THEN REAL_ARITH_TAC; REWRITE_TAC [ADD1] THEN STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `x (n + 1) * (sum (1..n) x / &n) pow n` THEN ASM_SIMP_TAC [LEMMA_3; GSYM REAL_OF_NUM_ADD; LE_1; ARITH_RULE `i <= n ==> i <= n + 1`] THEN GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC [LE_REFL; LE_1; ARITH_RULE `i <= n ==> i <= n + 1`]]);;
