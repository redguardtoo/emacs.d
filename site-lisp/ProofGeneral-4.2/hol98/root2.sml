(* Example proof by Konrad Slind.  See http://www.cs.kun.nl/~freek/comparison/ 
   Taken from HOL4 distribution hol98/examples/root2.sml *)

(*---------------------------------------------------------------------------*)
(* Challenge from Freek Wiedijk: the square root of two is not rational.     *)
(* I've adapted a proof in HOL Light by John Harrison.                       *)
(*---------------------------------------------------------------------------*)
 
load "transcTheory";   open arithmeticTheory BasicProvers;

(*---------------------------------------------------------------------------*)
(* Need a predicate on reals that picks out the rational ones                *)
(*---------------------------------------------------------------------------*)

val Rational_def = Define `Rational r = ?p q. ~(q=0) /\ (abs(r) = &p / &q)`;

(*---------------------------------------------------------------------------*)
(* Trivial lemmas                                                            *)
(*---------------------------------------------------------------------------*)

val EXP_2 = Q.prove(`!n:num. n**2 = n*n`,
  REWRITE_TAC [TWO,ONE,EXP] THEN RW_TAC arith_ss []);

val EXP2_LEM = Q.prove(`!x y:num. ((2*x)**2 = 2*(y**2)) = (2*(x**2) = y**2)`,
 REWRITE_TAC [TWO,EXP_2]
 THEN PROVE_TAC [MULT_MONO_EQ,MULT_ASSOC,MULT_SYM]);

(*---------------------------------------------------------------------------*)
(* Lemma: squares are not doublings of squares, except trivially.            *)
(*---------------------------------------------------------------------------*)

val lemma = Q.prove
(`!m n. (m**2 = 2 * n**2) ==> (m=0) /\ (n=0)`,
 completeInduct_on `m` THEN NTAC 2 STRIP_TAC THEN
  `?k. m = 2*k`      by PROVE_TAC[EVEN_DOUBLE,EXP_2,EVEN_MULT,EVEN_EXISTS] 
                     THEN VAR_EQ_TAC THEN
  `?p. n = 2*p`      by PROVE_TAC[EVEN_DOUBLE,EXP_2,EVEN_MULT,
                                  EVEN_EXISTS,EXP2_LEM] 
                     THEN VAR_EQ_TAC THEN
  `k**2 = 2*(p**2)`  by PROVE_TAC [EXP2_LEM] THEN
  `(k=0) \/ k < 2*k` by numLib.ARITH_TAC
 THENL [FULL_SIMP_TAC arith_ss [EXP_2],
        PROVE_TAC [MULT_EQ_0, DECIDE (Term `~(2 = 0n)`)]]);

(*---------------------------------------------------------------------------*)
(* The proof moves the problem from R to N, then uses lemma                  *)
(*---------------------------------------------------------------------------*)

local open realTheory transcTheory
in
val SQRT_2_IRRATIONAL = Q.prove
(`~Rational (sqrt 2r)`,
 RW_TAC std_ss [Rational_def,abs,SQRT_POS_LE,REAL_POS]
  THEN Cases_on `q = 0` THEN ASM_REWRITE_TAC []
  THEN SPOSE_NOT_THEN (MP_TAC o Q.AP_TERM `\x. x pow 2`)
  THEN RW_TAC arith_ss [SQRT_POW_2, REAL_POS, REAL_POW_DIV,
                        REAL_EQ_RDIV_EQ,REAL_LT, REAL_POW_LT]
  THEN REWRITE_TAC [REAL_OF_NUM_POW, REAL_MUL, REAL_INJ]
  THEN PROVE_TAC [lemma])
end;

(*---------------------------------------------------------------------------*)
(* The following is a bit more declarative                                   *)
(*---------------------------------------------------------------------------*)

infix THEN1;
fun ie q tac = Q_TAC SUFF_TAC q THEN1 tac;

local open realTheory transcTheory
in
val SQRT_2_IRRATIONAL = Q.prove
(`~Rational (sqrt 2r)`,
 ie `!p q. ~(q=0) ==> ~(sqrt 2 = & p / & q)` 
             (RW_TAC std_ss [Rational_def,abs,SQRT_POS_LE,REAL_POS] 
               THEN PROVE_TAC[]) THEN RW_TAC std_ss [] THEN
 ie `~(sqrt 2 = & p / & q)` (PROVE_TAC []) THEN 
 ie `~(2 * q**2 = p**2)` 
             (DISCH_TAC THEN SPOSE_NOT_THEN (MP_TAC o Q.AP_TERM `\x. x pow 2`) 
              THEN RW_TAC arith_ss [SQRT_POW_2,REAL_POS,
                          REAL_POW_DIV,REAL_EQ_RDIV_EQ,REAL_LT, REAL_POW_LT] 
              THEN ASM_REWRITE_TAC [REAL_OF_NUM_POW, REAL_MUL,REAL_INJ])
  THEN PROVE_TAC [lemma])
end;
