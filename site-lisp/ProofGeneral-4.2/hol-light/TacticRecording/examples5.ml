(* Taken from Library/prime.ml   *)

prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* HOL88 compatibility (since all this is a port of old HOL88 stuff).        *)
(* ------------------------------------------------------------------------- *)

let MULT_MONO_EQ = prove
 (`!m i n. ((SUC n) * m = (SUC n) * i) <=> (m = i)`,
  REWRITE_TAC[EQ_MULT_LCANCEL; NOT_SUC]);;

let LESS_ADD_1 = prove
 (`!m n. n < m ==> (?p. m = n + (p + 1))`,
  REWRITE_TAC[LT_EXISTS; ADD1; ADD_ASSOC]);;

let LESS_ADD_SUC = ARITH_RULE `!m n. m < (m + (SUC n))`;;

let LESS_0_CASES = ARITH_RULE `!m. (0 = m) \/ 0 < m`;;

let LESS_MONO_ADD = ARITH_RULE `!m n p. m < n ==> (m + p) < (n + p)`;;

let LESS_EQ_0 = prove
 (`!n. n <= 0 <=> (n = 0)`,
  REWRITE_TAC[LE]);;

let LESS_LESS_CASES = ARITH_RULE `!m n. (m = n) \/ m < n \/ n < m`;;

let LESS_ADD_NONZERO = ARITH_RULE `!m n. ~(n = 0) ==> m < (m + n)`;;

let NOT_EXP_0 = prove
 (`!m n. ~((SUC n) EXP m = 0)`,
  REWRITE_TAC[EXP_EQ_0; NOT_SUC]);;

let LESS_THM = ARITH_RULE `!m n. m < (SUC n) <=> (m = n) \/ m < n`;;

let NOT_LESS_0 = ARITH_RULE `!n. ~(n < 0)`;;

let ZERO_LESS_EXP = prove
 (`!m n. 0 < ((SUC n) EXP m)`,
  REWRITE_TAC[LT_NZ; NOT_EXP_0]);;

(* ------------------------------------------------------------------------- *)
(* General arithmetic lemmas.                                                *)
(* ------------------------------------------------------------------------- *)

let MULT_FIX = prove(
  `!x y. (x * y = x) <=> (x = 0) \/ (y = 1)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(SPEC `x:num` num_CASES) THEN
  REWRITE_TAC[MULT_CLAUSES; NOT_SUC] THEN
  REWRITE_TAC[GSYM(el 4 (CONJUNCTS (SPEC_ALL MULT_CLAUSES)))] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV)     (* MMA: this is a problem !!!!)
   [GSYM(el 3 (CONJUNCTS(SPEC_ALL MULT_CLAUSES)))] THEN
  MATCH_ACCEPT_TAC MULT_MONO_EQ);;

let LESS_EQ_MULT = prove(
  `!m n p q. m <= n /\ p <= q ==> (m * p) <= (n * q)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[LE_EXISTS]) THEN
  ASM_REWRITE_TAC[LEFT_ADD_DISTRIB; RIGHT_ADD_DISTRIB;
    GSYM ADD_ASSOC; LE_ADD]);;

let LESS_MULT = prove(
  `!m n p q. m < n /\ p < q ==> (m * p) < (n * q)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN
   ((CHOOSE_THEN SUBST_ALL_TAC) o MATCH_MP LESS_ADD_1)) THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; RIGHT_ADD_DISTRIB] THEN
  REWRITE_TAC[GSYM ADD1; MULT_CLAUSES; ADD_CLAUSES; GSYM ADD_ASSOC] THEN
  ONCE_REWRITE_TAC[GSYM (el 3 (CONJUNCTS ADD_CLAUSES))] THEN
  MATCH_ACCEPT_TAC LESS_ADD_SUC);;

let MULT_LCANCEL = prove(
  `!a b c. ~(a = 0) /\ (a * b = a * c) ==> (b = c)`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC(SPEC `a:num` num_CASES) THEN
  REWRITE_TAC[NOT_SUC; MULT_MONO_EQ]);;

let LT_POW2_REFL = prove
 (`!n. n < 2 EXP n`,
  INDUCT_TAC THEN REWRITE_TAC[EXP] THEN TRY(POP_ASSUM MP_TAC) THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Properties of the exponential function.                                   *)
(* ------------------------------------------------------------------------- *)

let EXP_0 = prove
 (`!n. 0 EXP (SUC n) = 0`,
  REWRITE_TAC[EXP; MULT_CLAUSES]);;

let EXP_MONO_LT_SUC = prove
 (`!n x y. (x EXP (SUC n)) < (y EXP (SUC n)) <=> (x < y)`,
  REWRITE_TAC[EXP_MONO_LT; NOT_SUC]);;

let EXP_MONO_LE_SUC = prove
 (`!x y n. (x EXP (SUC n)) <= (y EXP (SUC n)) <=> x <= y`,
  REWRITE_TAC[EXP_MONO_LE; NOT_SUC]);;

let EXP_MONO_EQ_SUC = prove
 (`!x y n. (x EXP (SUC n) = y EXP (SUC n)) <=> (x = y)`,
  REWRITE_TAC[EXP_MONO_EQ; NOT_SUC]);;

let EXP_EXP = prove
 (`!x m n. (x EXP m) EXP n = x EXP (m * n)`,
  REWRITE_TAC[EXP_MULT]);;

(* ------------------------------------------------------------------------- *)
(* More ad-hoc arithmetic lemmas unlikely to be useful elsewhere.            *)
(* ------------------------------------------------------------------------- *)

let DIFF_LEMMA = prove(
  `!a b. a < b ==> (a = 0) \/ (a + (b - a)) < (a + b)`,
  REPEAT GEN_TAC THEN
  DISJ_CASES_TAC(SPEC `a:num` LESS_0_CASES) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CHOOSE_THEN SUBST1_TAC o MATCH_MP LESS_ADD_1) THEN
  DISJ2_TAC THEN REWRITE_TAC[ONCE_REWRITE_RULE[ADD_SYM] ADD_SUB] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM (CONJUNCT1 ADD_CLAUSES)] THEN
  REWRITE_TAC[ADD_ASSOC] THEN
  REPEAT(MATCH_MP_TAC LESS_MONO_ADD) THEN POP_ASSUM ACCEPT_TAC);;

let NOT_EVEN_EQ_ODD = prove(
  `!m n. ~(2 * m = SUC(2 * n))`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o AP_TERM `EVEN`) THEN
  REWRITE_TAC[EVEN; EVEN_MULT; ARITH]);;

let CANCEL_TIMES2 = prove(
  `!x y. (2 * x = 2 * y) <=> (x = y)`,
  REWRITE_TAC[num_CONV `2`; MULT_MONO_EQ]);;

let EVEN_SQUARE = prove(
  `!n. EVEN(n) ==> ?x. n EXP 2 = 4 * x`,
  GEN_TAC THEN REWRITE_TAC[EVEN_EXISTS] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` SUBST1_TAC) THEN
  EXISTS_TAC `m * m` THEN REWRITE_TAC[EXP_2] THEN
  REWRITE_TAC[SYM(REWRITE_CONV[ARITH] `2 * 2`)] THEN
  REWRITE_TAC[MULT_AC]);;

let ODD_SQUARE = prove(
  `!n. ODD(n) ==> ?x. n EXP 2 = (4 * x) + 1`,
  GEN_TAC THEN REWRITE_TAC[ODD_EXISTS] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` SUBST1_TAC) THEN
  ASM_REWRITE_TAC[EXP_2; MULT_CLAUSES; ADD_CLAUSES] THEN
  REWRITE_TAC[GSYM ADD1; SUC_INJ] THEN
  EXISTS_TAC `(m * m) + m` THEN
  REWRITE_TAC(map num_CONV [`4`; `3`; `2`; `1`]) THEN
  REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; RIGHT_ADD_DISTRIB] THEN
  REWRITE_TAC[ADD_AC]);;

let DIFF_SQUARE = prove(
  `!x y. (x EXP 2) - (y EXP 2) = (x + y) * (x - y)`,
  REPEAT GEN_TAC THEN
  DISJ_CASES_TAC(SPECL [`x:num`; `y:num`] LE_CASES) THENL
   [SUBGOAL_THEN `(x * x) <= (y * y)` MP_TAC THENL
     [MATCH_MP_TAC LESS_EQ_MULT THEN ASM_REWRITE_TAC[];
      POP_ASSUM MP_TAC THEN REWRITE_TAC[GSYM SUB_EQ_0] THEN
      REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[EXP_2; MULT_CLAUSES]];
    POP_ASSUM(CHOOSE_THEN SUBST1_TAC o REWRITE_RULE[LE_EXISTS]) THEN
    REWRITE_TAC[ONCE_REWRITE_RULE[ADD_SYM] ADD_SUB] THEN
    REWRITE_TAC[EXP_2; LEFT_ADD_DISTRIB; RIGHT_ADD_DISTRIB] THEN
    REWRITE_TAC[GSYM ADD_ASSOC; ONCE_REWRITE_RULE[ADD_SYM] ADD_SUB] THEN
    AP_TERM_TAC THEN GEN_REWRITE_TAC LAND_CONV [ADD_SYM] THEN
    AP_TERM_TAC THEN MATCH_ACCEPT_TAC MULT_SYM]);;

let ADD_IMP_SUB = prove(
  `!x y z. (x + y = z) ==> (x = z - y)`,
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[ADD_SUB]);;

let ADD_SUM_DIFF = prove(
  `!v w. v <= w ==> ((w + v) - (w - v) = 2 * v) /\
                    ((w + v) + (w - v) = 2 * w)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LE_EXISTS] THEN
  DISCH_THEN(CHOOSE_THEN SUBST1_TAC) THEN
  REWRITE_TAC[ONCE_REWRITE_RULE[ADD_SYM] ADD_SUB] THEN
  REWRITE_TAC[MULT_2; GSYM ADD_ASSOC] THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN
  REWRITE_TAC[ONCE_REWRITE_RULE[ADD_SYM] ADD_SUB; GSYM ADD_ASSOC]);;

let EXP_4 = prove(
  `!n. n EXP 4 = (n EXP 2) EXP 2`,
  GEN_TAC THEN REWRITE_TAC[EXP_EXP] THEN
  REWRITE_TAC[ARITH]);;
