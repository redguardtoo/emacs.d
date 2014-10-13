(* ========================================================================== *)
(* PROMOTTION (HOL LIGHT)                                                     *)
(* - Overwrites original HOL Light tactics/etc with xgoal/xthm versions       *)
(*                                                                            *)
(* By Mark Adams                                                              *)
(* Copyright (c) Univeristy of Edinburgh, 2012                                *)
(* ========================================================================== *)



(* ** TACTICS.ML ** *)


(* Tactics *)

(* Atomic tactics can be automatically promoted to deal with xgoals and       *)
(* recording.                                                                 *)

let NO_TAC = tactic_wrap "NO_TAC" NO_TAC;;
let ALL_TAC = tactic_wrap "ALL_TAC" ALL_TAC;;

let LABEL_TAC = stringthm_tactic_wrap "LABEL_TAC" LABEL_TAC;;
let ASSUME_TAC = thm_tactic_wrap "ASSUME_TAC" ASSUME_TAC;;

let ACCEPT_TAC = thm_tactic_wrap "ACCEPT_TAC" ACCEPT_TAC;;

let CONV_TAC = conv_tactic_wrap "CONV_TAC" CONV_TAC;;

let REFL_TAC = tactic_wrap "REFL_TAC" REFL_TAC;;
let ABS_TAC = tactic_wrap "ABS_TAC" ABS_TAC;;
let MK_COMB_TAC = tactic_wrap "MK_COMB_TAC" MK_COMB_TAC;;
let AP_TERM_TAC = tactic_wrap "AP_TERM_TAC" AP_TERM_TAC;;
let AP_THM_TAC = tactic_wrap "AP_THM_TAC" AP_THM_TAC;;
let BINOP_TAC = tactic_wrap "BINOP_TAC" BINOP_TAC;;
let SUBST1_TAC = thm_tactic_wrap "SUBST1_TAC" SUBST1_TAC;;
let SUBST_ALL_TAC = thm_tactic_wrap "SUBST_ALL_TAC" SUBST_ALL_TAC;;
let BETA_TAC = tactic_wrap "BETA_TAC" BETA_TAC;;

let SUBST_VAR_TAC = thm_tactic_wrap "SUBST_VAR_TAC" SUBST_VAR_TAC;;

let DISCH_TAC = tactic_wrap "DISCH_TAC" DISCH_TAC;;
let MP_TAC = thm_tactic_wrap "MP_TAC" MP_TAC;;
let EQ_TAC = tactic_wrap "EQ_TAC" EQ_TAC;;
let UNDISCH_TAC = term_tactic_wrap "UNDISCH_TAC" UNDISCH_TAC;;
let SPEC_TAC = termpair_tactic_wrap "SPEC_TAC" SPEC_TAC;;
let X_GEN_TAC = term_tactic_wrap "X_GEN_TAC" X_GEN_TAC;;
let GEN_TAC = tactic_wrap "GEN_TAC" GEN_TAC;;
let EXISTS_TAC = term_tactic_wrap "EXISTS_TAC" EXISTS_TAC;;
let CHOOSE_TAC = thm_tactic_wrap "CHOOSE_TAC" CHOOSE_TAC;;
let CONJ_TAC = tactic_wrap "CONJ_TAC" CONJ_TAC;;
let DISJ1_TAC = tactic_wrap "DISJ1_TAC" DISJ1_TAC;;
let DISJ2_TAC = tactic_wrap "DISJ2_TAC" DISJ2_TAC;;
let DISJ_CASES_TAC = thm_tactic_wrap "DISJ_CASES_TAC" DISJ_CASES_TAC;;
let CONTR_TAC = thm_tactic_wrap "CONTR_TAC" CONTR_TAC;;
let MATCH_ACCEPT_TAC = thm_tactic_wrap "MATCH_ACCEPT_TAC" MATCH_ACCEPT_TAC;;
let MATCH_MP_TAC = thm_tactic_wrap "MATCH_MP_TAC" MATCH_MP_TAC;;

let STRIP_ASSUME_TAC = thm_tactic_wrap "STRIP_ASSUME_TAC" STRIP_ASSUME_TAC;;
let STRUCT_CASES_TAC = thm_tactic_wrap "STRUCT_CASES_TAC" STRUCT_CASES_TAC;;
let STRIP_TAC = tactic_wrap "STRIP_TAC" STRIP_TAC;;

let X_META_EXISTS_TAC = term_tactic_wrap "X_META_EXISTS_TAC" X_META_EXISTS_TAC;;
let META_EXISTS_TAC = tactic_wrap "META_EXISTS_TAC" META_EXISTS_TAC;;

let ANTS_TAC = tactic_wrap "ANTS_TAC" ANTS_TAC;;


(* Special cases, already fully hand-promoted *)

let SUBGOAL_THEN = xSUBGOAL_THEN;;


(* Tacticals *)

(* Tacticals need to be hand-promoted to deal with xgoals, but this is        *)
(* trivial and is done in 'xtactics.ml'.  They are further promoted here to   *)
(* get recorded as boxes, using the tactical-wrap functions.                  *)

let (THEN) = btactical_wrap "THEN" (xTHEN);;
let (THENL) = btactical_wrap "THENL" (xTHENL);;
let (ORELSE) = btactical_wrap "ORELSE" (xORELSE);;
let TRY = tactical_wrap "TRY" xTRY;;
let REPEAT = tactical_wrap "REPEAT" xREPEAT;;
let EVERY = tactical_wrap "EVERY" xEVERY;;
let FIRST = tactical_wrap "FIRST" xFIRST;;
let MAP_EVERY = list_tactical_wrap "MAP_EVERY" xMAP_EVERY;;
let MAP_FIRST = list_tactical_wrap "MAP_FIRST" xMAP_FIRST;;
let CHANGED_TAC = tactical_wrap "CHANGED_TAC" xCHANGED_TAC;;
let REPLICATE_TAC = int_tactical_wrap "REPLICATE_TAC" xREPLICATE_TAC;;


(* Subgoal commands *)

let e = xe;;
let r = xr;;
let set_goal = xset_goal;;
let g = xg;;
let b = xb;;
let p = xp;;
let top_goal = xtop_goal;;
let top_thm = xtop_thm;;

let prove = xprove;;



(* ** COMMON HOL API ** *)


(* Rules *)

let ADD_ASSUM = term_rule_wrap "ADD_ASSUM" ADD_ASSUM;;
let ASSUME = conv_wrap "ASSUME" ASSUME;;
let BETA_CONV = conv_wrap "BETA_CONV" BETA_CONV;;
let CCONTR = term_rule_wrap "CCONTR" CCONTR;;
let CHOOSE = termthmpair_rule_wrap "CHOOSE" CHOOSE;;
let CONJ = drule_wrap "CONJ" CONJ;;
let CONJUNCT1 = rule_wrap "CONJUNCT1" CONJUNCT1;;
let CONJUNCT2 = rule_wrap "CONJUNCT2" CONJUNCT2;;
let CONTR = term_rule_wrap "CONTR" CONTR;;
let DEDUCT_ANTISYM_RULE = drule_wrap "DEDUCT_ANTISYM_RULE" DEDUCT_ANTISYM_RULE;;
let DISCH = term_rule_wrap "DISCH" DISCH;;
let DISJ1 = thm_conv_wrap "DISJ1" DISJ1;;
let DISJ2 = term_rule_wrap "DISJ2" DISJ2;;
let DISJ_CASES = trule_wrap "DISJ_CASES" DISJ_CASES;;
let EQ_MP = drule_wrap "EQ_MP" EQ_MP;;
let EQF_INTRO = rule_wrap "EQF_INTRO" EQF_INTRO;;
let EQF_ELIM = rule_wrap "EQF_ELIM" EQF_ELIM;;
let EQT_INTRO = rule_wrap "EQT_INTRO" EQT_INTRO;;
let EQT_ELIM = rule_wrap "EQT_ELIM" EQT_ELIM;;
let ETA_CONV = conv_wrap "ETA_CONV" ETA_CONV;;
let EXISTS = termpair_rule_wrap "EXISTS" EXISTS;;
let GEN = term_rule_wrap "GEN" GEN;;
let GENL = termlist_rule_wrap "GENL" GENL;;
let IMP_ANTISYM_RULE = drule_wrap "IMP_ANTISYM_RULE" IMP_ANTISYM_RULE;;
let IMP_TRANS = drule_wrap "IMP_TRANS" IMP_TRANS;;
let INST = terminst_rule_wrap "INST" INST;;
let INST_TYPE = typeinst_rule_wrap "INST_TYPE" INST_TYPE;;
let MP = drule_wrap "MP" MP;;
let NOT_ELIM = rule_wrap "NOT_ELIM" NOT_ELIM;;
let NOT_INTRO = rule_wrap "NOT_INTRO" NOT_INTRO;;
let PROVE_HYP = drule_wrap "PROVE_HYP" PROVE_HYP;;
let REFL = conv_wrap "REFL" REFL;;
let SELECT_RULE = rule_wrap "SELECT_RULE" SELECT_RULE;;
let SPEC = term_rule_wrap "SPEC" SPEC;;
let SPECL = termlist_rule_wrap "SPECL" SPECL;;
let SUBS = thmlist_rule_wrap "SUBS" SUBS;;
let SUBS_CONV = thmlist_conv_wrap "SUBS_CONV" SUBS_CONV;;
let SYM = rule_wrap "SYM" SYM;;
let SYM_CONV = conv_wrap "SYM_CONV" SYM_CONV;;
let TRANS = drule_wrap "TRANS" TRANS;;
let UNDISCH = rule_wrap "UNDISCH" UNDISCH;;

let ABS = term_rule_wrap "ABS" ABS;;
let MK_COMB = prule_wrap "MK_COMB" MK_COMB;;
let AP_THM = thm_conv_wrap "AP_THM" AP_THM;;
let AP_TERM = term_rule_wrap "AP_TERM" AP_TERM;;

let NUM_SUC_CONV = conv_wrap "NUM_SUC_CONV" NUM_SUC_CONV;;
let NUM_PRE_CONV = conv_wrap "NUM_PRE_CONV" NUM_PRE_CONV;;
let NUM_ADD_CONV = conv_wrap "NUM_ADD_CONV" NUM_ADD_CONV;;
let NUM_SUB_CONV = conv_wrap "NUM_SUB_CONV" NUM_SUB_CONV;;
let NUM_MULT_CONV = conv_wrap "NUM_MULT_CONV" NUM_MULT_CONV;;
let NUM_EXP_CONV = conv_wrap "NUM_EXP_CONV" NUM_EXP_CONV;;
let NUM_EQ_CONV = conv_wrap "NUM_EQ_CONV" NUM_EQ_CONV;;
let NUM_LT_CONV = conv_wrap "NUM_LT_CONV" NUM_LT_CONV;;
let NUM_LE_CONV = conv_wrap "NUM_LE_CONV" NUM_LE_CONV;;
let NUM_GT_CONV = conv_wrap "NUM_GT_CONV" NUM_GT_CONV;;
let NUM_EVEN_CONV = conv_wrap "NUM_EVEN_CONV" NUM_EVEN_CONV;;
let NUM_ODD_CONV = conv_wrap "NUM_ODD_CONV" NUM_ODD_CONV;;


(* Theorems *)

let ETA_AX = theorem_wrap "ETA_AX" ETA_AX;;
let INFINITY_AX = theorem_wrap "INFINITY_AX" INFINITY_AX;;
let BOOL_CASES_AX = theorem_wrap "BOOL_CASES_AX" BOOL_CASES_AX;;
let SELECT_AX = theorem_wrap "SELECT_AX" SELECT_AX;;
let TRUTH = theorem_wrap "TRUTH" TRUTH;;
let EXCLUDED_MIDDLE = theorem_wrap "EXCLUDED_MIDDLE" EXCLUDED_MIDDLE;;

let PAIR_EQ = theorem_wrap "PAIR_EQ" PAIR_EQ;;
let PAIR_SURJECTIVE = theorem_wrap "PAIR_SURJECTIVE" PAIR_SURJECTIVE;;
let FST = theorem_wrap "FST" FST;;
let SND = theorem_wrap "SND" SND;;

let IND_SUC_0 = theorem_wrap "IND_SUC_0" IND_SUC_0;;
let IND_SUC_INJ = theorem_wrap "IND_SUC_INJ" IND_SUC_INJ;;

let NOT_SUC = theorem_wrap "NOT_SUC" NOT_SUC;;
let SUC_INJ = theorem_wrap "SUC_INJ" SUC_INJ;;
let num_INDUCTION = theorem_wrap "num_INDUCTION" num_INDUCTION;;
let num_CASES = theorem_wrap "num_CASES" num_CASES;;
let num_RECURSION = theorem_wrap "num_RECURSION" num_RECURSION;;
let PRE = theorem_wrap "PRE" PRE;;
let ADD = theorem_wrap "ADD" ADD;;
let SUB = theorem_wrap "SUB" SUB;;
let MULT = theorem_wrap "MULT" MULT;;
let EXP = theorem_wrap "EXP" EXP;;
let LT = theorem_wrap "LT" LT;;
let LE = theorem_wrap "LE" LE;;
let GT = theorem_wrap "GT" GT;;
let GE = theorem_wrap "GE" GE;;
let EVEN = theorem_wrap "EVEN" EVEN;;
let ODD = theorem_wrap "ODD" ODD;;



(* ** OTHER HOL LIGHT ** *)


(* More tactics *)

let REWRITE_TAC = thmlist_tactic_wrap "REWRITE_TAC" REWRITE_TAC;;
let PURE_REWRITE_TAC = thmlist_tactic_wrap "PURE_REWRITE_TAC" PURE_REWRITE_TAC;;
let ONCE_REWRITE_TAC = thmlist_tactic_wrap "ONCE_REWRITE_TAC" ONCE_REWRITE_TAC;;
let ASM_REWRITE_TAC = thmlist_tactic_wrap "ASM_REWRITE_TAC" ASM_REWRITE_TAC;;
let PURE_ASM_REWRITE_TAC =
        thmlist_tactic_wrap "PURE_ASM_REWRITE_TAC" PURE_ASM_REWRITE_TAC;;
let ONCE_ASM_REWRITE_TAC =
        thmlist_tactic_wrap "ONCE_ASM_REWRITE_TAC" ONCE_ASM_REWRITE_TAC;;
let GEN_REWRITE_TAC =
        convconvthmlist_tactic_wrap "GEN_REWRITE_TAC" GEN_REWRITE_TAC;;
let SIMP_TAC = thmlist_tactic_wrap "SIMP_TAC" SIMP_TAC;;
let PURE_SIMP_TAC = thmlist_tactic_wrap "PURE_SIMP_TAC" PURE_SIMP_TAC;;
let ONCE_SIMP_TAC = thmlist_tactic_wrap "ONCE_SIMP_TAC" ONCE_SIMP_TAC;;
let ASM_SIMP_TAC = thmlist_tactic_wrap "ASM_SIMP_TAC" ASM_SIMP_TAC;;
let PURE_ASM_SIMP_TAC =
        thmlist_tactic_wrap "PURE_ASM_SIMP_TAC" PURE_ASM_SIMP_TAC;;
let ONCE_ASM_SIMP_TAC =
        thmlist_tactic_wrap "ONCE_ASM_SIMP_TAC" ONCE_ASM_SIMP_TAC;;
let ABBREV_TAC = term_tactic_wrap "ABBREV_TAC" ABBREV_TAC;;
let EXPAND_TAC = string_tactic_wrap "EXPAND_TAC" EXPAND_TAC;;

let ASM_CASES_TAC = term_tactic_wrap "ASM_CASES_TAC" ASM_CASES_TAC;;
let COND_CASES_TAC = tactic_wrap "COND_CASES_TAC" COND_CASES_TAC;;

let ARITH_TAC = tactic_wrap "ARITH_TAC" ARITH_TAC;;
let INDUCT_TAC = tactic_wrap "INDUCT_TAC" INDUCT_TAC;;

let REAL_ARITH_TAC = tactic_wrap "REAL_ARITH_TAC" REAL_ARITH_TAC;;
let ASM_REAL_ARITH_TAC = tactic_wrap "ASM_REAL_ARITH_TAC" ASM_REAL_ARITH_TAC;;


(* More rules *)

let RATOR_CONV = conv_conv_wrap "RATOR_CONV" RATOR_CONV;;
let RAND_CONV = conv_conv_wrap "RAND_CONV" RAND_CONV;;
let LAND_CONV = conv_conv_wrap "LAND_CONV" LAND_CONV;;
let ABS_CONV = conv_conv_wrap "ABS_CONV" ABS_CONV;;
let BINDER_CONV = conv_conv_wrap "BINDER_CONV" BINDER_CONV;;
let SUB_CONV = conv_conv_wrap "SUB_CONV" SUB_CONV;;
let BINOP_CONV = conv_conv_wrap "BINOP_CONV" BINOP_CONV;;
let GSYM = rule_wrap "GSYM" GSYM;;
let CONJUNCTS = multirule_wrap "CONJUNCTS" CONJUNCTS;;
let SPEC_ALL = rule_wrap "SPEC_ALL" SPEC_ALL;;
let ISPECL = termlist_rule_wrap "ISPECL" ISPECL;;
let ALL_CONV = conv_wrap "ALL_CONV" ALL_CONV;;
let (REPEATC) = conv_conv_wrap "REPEATC" REPEATC;;
let ONCE_DEPTH_CONV = conv_conv_wrap "ONCE_DEPTH_CONV" ONCE_DEPTH_CONV;;

let REWRITE_RULE = thmlist_rule_wrap "REWRITE_RULE" REWRITE_RULE;;

let num_CONV = conv_wrap "num_CONV" num_CONV;;
let ARITH_RULE = conv_wrap "ARITH_RULE" ARITH_RULE;;

let REAL_ARITH = conv_wrap "REAL_ARITH" REAL_ARITH;;
let REAL_FIELD = conv_wrap "REAL_FIELD" REAL_FIELD;;


(* More theorems *)

let CONJ_ASSOC = theorem_wrap "CONJ_ASSOC" CONJ_ASSOC;;
let IMP_IMP = theorem_wrap "IMP_IMP" IMP_IMP;;
let EQ_IMP = theorem_wrap "EQ_IMP" EQ_IMP;;

let ARITH = theorem_wrap "ARITH" ARITH;;
let ARITH_EQ = theorem_wrap "ARITH_EQ" ARITH_EQ;;
let ADD_ASSOC = theorem_wrap "ADD_ASSOC" ADD_ASSOC;;
let ADD_CLAUSES = theorem_wrap "ADD_CLAUSES" ADD_CLAUSES;;
let LEFT_ADD_DISTRIB = theorem_wrap "LEFT_ADD_DISTRIB" LEFT_ADD_DISTRIB;;
let RIGHT_ADD_DISTRIB = theorem_wrap "RIGHT_ADD_DISTRIB" RIGHT_ADD_DISTRIB;;
let MULT_CLAUSES =theorem_wrap "MULT_CLAUSES" MULT_CLAUSES;;
let SUB_REFL = theorem_wrap "SUB_REFL" SUB_REFL;;
let ADD1 =  theorem_wrap "ADD1" ADD1;;
let EQ_MULT_LCANCEL = theorem_wrap "EQ_MULT_LCANCEL" EQ_MULT_LCANCEL;;
let LE_EXISTS = theorem_wrap "LE_EXISTS" LE_EXISTS;;
let LE_ADD = theorem_wrap "LE_ADD" LE_ADD;;
let LE_1 = theorem_wrap "LE_1" LE_1;;
let LE_REFL = theorem_wrap "LE_REFL" LE_REFL;;
let LT_SUC = theorem_wrap "LT_SUC" LT_SUC;;
let LT_EXISTS = theorem_wrap "LT_EXISTS" LT_EXISTS;;
let LT_NZ = theorem_wrap "LT_NZ" LT_NZ;;
let EXP_EQ_0 = theorem_wrap "EXP_EQ_0" EXP_EQ_0;;
let FACT = theorem_wrap "FACT" FACT;;
let  = theorem_wrap "" ;;

let REAL_ADD_LDISTRIB = theorem_wrap "REAL_ADD_LDISTRIB" REAL_ADD_LDISTRIB;;
let REAL_OF_NUM_ADD = theorem_wrap "REAL_OF_NUM_ADD" REAL_OF_NUM_ADD;;
let REAL_OF_NUM_EQ = theorem_wrap "REAL_OF_NUM_EQ" REAL_OF_NUM_EQ;;
let REAL_OF_NUM_SUC = theorem_wrap "REAL_OF_NUM_SUC" REAL_OF_NUM_SUC;;
let REAL_MUL_ASSOC = theorem_wrap "REAL_MUL_ASSOC" REAL_MUL_ASSOC;;
let REAL_MUL_SYM = theorem_wrap "REAL_MUL_SYM" REAL_MUL_SYM;;
let REAL_MUL_RID = theorem_wrap "REAL_MUL_RID" REAL_MUL_RID;;
let REAL_MUL_RZERO = theorem_wrap "REAL_MUL_RZERO" REAL_MUL_RZERO;;
let REAL_DIV_LMUL = theorem_wrap "REAL_DIV_LMUL" REAL_DIV_LMUL;;
let REAL_POS = theorem_wrap "REAL_POS" REAL_POS;;
let REAL_LE_TRANS = theorem_wrap "REAL_LE_TRANS" REAL_LE_TRANS;;
let REAL_LE_MUL = theorem_wrap "REAL_LE_MUL" REAL_LE_MUL;;
let REAL_LE_RMUL = theorem_wrap "REAL_LE_RMUL" REAL_LE_RMUL;;
let REAL_LE_DIV = theorem_wrap "REAL_LE_DIV" REAL_LE_DIV;;
let REAL_LE_SQUARE = theorem_wrap "REAL_LE_SQUARE" REAL_LE_SQUARE;;
let REAL_LE_RDIV_EQ = theorem_wrap "REAL_LE_RDIV_EQ" REAL_LE_RDIV_EQ;;
let real_pow = theorem_wrap "real_pow" real_pow;;
let REAL_POW_2 = theorem_wrap "REAL_POW_2" REAL_POW_2;;
let REAL_POW_ZERO = theorem_wrap "REAL_POW_ZERO" REAL_POW_ZERO;;
let REAL_POW_ADD = theorem_wrap "REAL_POW_ADD" REAL_POW_ADD;;
let REAL_POW_DIV = theorem_wrap "REAL_POW_DIV" REAL_POW_DIV;;
let REAL_POW_LE = theorem_wrap "REAL_POW_LE" REAL_POW_LE;;
let REAL_POW_LT = theorem_wrap "REAL_POW_LT" REAL_POW_LT;;
let SUM_RMUL = theorem_wrap "SUM_RMUL" SUM_RMUL;;
let SUM_ADD_SPLIT = theorem_wrap "SUM_ADD_SPLIT" SUM_ADD_SPLIT;;
let SUM_POS_LE_NUMSEG = theorem_wrap "SUM_POS_LE_NUMSEG" SUM_POS_LE_NUMSEG;;
let SUM_CLAUSES_NUMSEG = theorem_wrap "SUM_CLAUSES_NUMSEG" SUM_CLAUSES_NUMSEG;;
let SUM_SING_NUMSEG = theorem_wrap "SUM_SING_NUMSEG" SUM_SING_NUMSEG;;
let PRODUCT_CLAUSES_NUMSEG =
   theorem_wrap "PRODUCT_CLAUSES_NUMSEG" PRODUCT_CLAUSES_NUMSEG;;