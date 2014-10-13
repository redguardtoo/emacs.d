pg_mode_on ();;
get_pg_mode ();;

g `(?x:num. p(x) /\ q(x) /\ r(x)) ==> (?x. r(x) /\ p(x)) /\ (?x. p(x) /\ (q(x) <=> r(x)))`;;
e (STRIP_TAC);;
e (STRIP_TAC);;
e (X_META_EXISTS_TAC `n1:num` THEN CONJ_TAC);;
e (FIRST_X_ASSUM(UNIFY_ACCEPT_TAC [`n1:num`]));;
e (ASM_REWRITE_TAC[]);;
e (X_META_EXISTS_TAC `n2:num` THEN CONJ_TAC);;
e (FIRST_X_ASSUM(UNIFY_ACCEPT_TAC [`n2:num`]));;
e (ASM_REWRITE_TAC[]);;
let th = top_thm ();;
