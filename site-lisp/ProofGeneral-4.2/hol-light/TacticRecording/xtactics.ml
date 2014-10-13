(* ========================================================================= *)
(* HOL Light subgoal package amended for id-carrying goals.                  *)
(*                                                                           *)
(*       Mark Adams, School of Informatics, University of Edinburgh          *)
(*                                                                           *)
(* (c) Copyright, University of Edinburgh, 2012                              *)
(* ========================================================================= *)

(* The 'xgoal' variant of the 'goal' datatype is defined here, to label      *)
(* goals with a unique goal id.  This gives a basis for recording tactic     *)
(* proofs.  Variants of all the datatypes depending on 'goal', such as       *)
(* 'xgoalstate' and 'xtactic', are also defined, along with a variant        *)
(* subgoal package.  ML names are given an "x" prefix to keep them distinct  *)
(* from the originals for now (but originals are overwritten later, in       *)
(* 'install.ml').                                                            *)

(* The goal id counter is only adjusted in this file by being incremented in *)
(* 'mk_xgoalstate', used when starting a new subgoal package proof.          *)
(* Xtactics are assumed to give their resulting xgoals id labels based on an *)
(* appropriately updated goal id counter.                                    *)

(* After the implementation of xgoals themselves at the start of this file,  *)
(* the rest of the file is more-or-less copied verbatim from HOL Light's     *)
(* original 'tactics.ml', with just a few changes required.  This enables an *)
(* easy diff operation with the original if required to check that the       *)
(* changes are valid.                                                        *)

(* ------------------------------------------------------------------------- *)
(* Goal counter for providing goal ids.                                      *)
(* ------------------------------------------------------------------------- *)

type goalid = int;;

let string_of_goal_id (id:goalid) = string_of_int id;;

let the_goal_id_counter = ref (0 : goalid);;

let inc_goal_id_counter () =
  (the_goal_id_counter := !the_goal_id_counter + 1);;

(* ------------------------------------------------------------------------- *)
(* An xgoal extends a goal with an identity.                                 *)
(* ------------------------------------------------------------------------- *)

type xgoal = goal * goalid;;

let equals_xgoal (((a,w),_):xgoal) (((a',w'),_):xgoal) =
  forall2 (fun (s,th) (s',th') -> s = s' & equals_thm th th') a a' & w = w';;

let mk_xgoal (gn:goal*goalid) : xgoal = gn;;

let dest_xgoal (gn:xgoal) : goal*goalid = gn;;

let xgoal_goal ((g,id):xgoal) : goal  = g;;

let xgoal_id ((g,id):xgoal) : goalid  = id;;

(* ------------------------------------------------------------------------- *)
(* The xgoalstate is like goalstate but for xgoals instead of goals.         *)
(* ------------------------------------------------------------------------- *)

type xgoalstate = (term list * instantiation) * xgoal list * justification;;

(* ------------------------------------------------------------------------- *)
(* A goalstack but for xgoals.                                               *)
(* ------------------------------------------------------------------------- *)

type xgoalstack = xgoalstate list;;

(* ------------------------------------------------------------------------- *)
(* Refinements for xgoals.                                                   *)
(* ------------------------------------------------------------------------- *)

type xrefinement = xgoalstate -> xgoalstate;;

(* ------------------------------------------------------------------------- *)
(* Tactics for xgoals.                                                       *)
(* ------------------------------------------------------------------------- *)

type xtactic = xgoal -> xgoalstate;;

type xthm_tactic = xthm -> xtactic;;

type xthm_tactical = xthm_tactic -> xthm_tactic;;

(* ------------------------------------------------------------------------- *)
(* Instantiation of xgoals.                                                  *)
(* ------------------------------------------------------------------------- *)

let (inst_xgoal:instantiation->xgoal->xgoal) =
  fun p ((thms,w),id) ->
    (map (I F_F INSTANTIATE_ALL p) thms,instantiate p w),id;;

(* ------------------------------------------------------------------------- *)
(* Validity check for xtactics.                                              *)
(* ------------------------------------------------------------------------- *)

let (xVALID:xtactic->xtactic) =
  let fake_thm ((asl,w),id) =
    let asms = itlist (union o hyp o snd) asl [] in
    mk_fthm(asms,w)
  and false_tm = `_FALSITY_` in
  fun tac ((asl,w),id) ->
    let ((mvs,i),gls,just as res) = tac ((asl,w),id) in
    let ths = map fake_thm gls in
    let asl',w' = dest_thm(just null_inst ths) in
    let asl'',w'' = inst_goal i (asl,w) in
    let maxasms =
      itlist (fun (_,th) -> union (insert (concl th) (hyp th))) asl'' [] in
    if aconv w' w'' & forall (C mem maxasms) (subtract asl' [false_tm])
    then res else failwith "VALID: Invalid tactic";;

(* ------------------------------------------------------------------------- *)
(* Various simple combinators for tactics, identity tactic etc.              *)
(* ------------------------------------------------------------------------- *)

let (xTHEN),(xTHENL) =
  let propagate_empty i [] = []
  and propagate_thm th i [] = INSTANTIATE_ALL i th in
  let compose_justs n just1 just2 i ths =
    let ths1,ths2 = chop_list n ths in
    (just1 i ths1)::(just2 i ths2) in
  let rec seqapply l1 l2 = match (l1,l2) with
     ([],[]) -> null_meta,[],propagate_empty
   | ((tac:xtactic)::tacs),((goal:xgoal)::goals) ->
            let ((mvs1,insts1),gls1,just1 as gstate1) = tac goal in
            let goals' = map (inst_xgoal insts1) goals in
            let ((mvs2,insts2),gls2,just2 as gstate2) = seqapply tacs goals' in
            ((union mvs1 mvs2,compose_insts insts1 insts2),
             gls1@gls2,compose_justs (length gls1) just1 just2)
   | _,_ -> failwith "seqapply: Length mismatch" in
  let justsequence just1 just2 insts2 i ths =
    just1 (compose_insts insts2 i) (just2 i ths) in
  let tacsequence ((mvs1,insts1),gls1,just1 as gstate1) tacl =
    let ((mvs2,insts2),gls2,just2 as gstate2) = seqapply tacl gls1 in
    let jst = justsequence just1 just2 insts2 in
    let just = if gls2 = [] then propagate_thm (jst null_inst []) else jst in
    ((union mvs1 mvs2,compose_insts insts1 insts2),gls2,just) in
  let (then_: xtactic -> xtactic -> xtactic) =
    fun tac1 tac2 g ->
      let _,gls,_ as gstate = tac1 g in
      tacsequence gstate (replicate tac2 (length gls))
  and (thenl_: xtactic -> xtactic list -> xtactic) =
    fun tac1 tac2l g ->
      let _,gls,_ as gstate = tac1 g in
      if gls = [] then tacsequence gstate []
      else tacsequence gstate tac2l in
  then_,thenl_;;

let ((xORELSE): xtactic -> xtactic -> xtactic) =
  fun tac1 tac2 g ->
    try tac1 g with Failure _ -> tac2 g;;

let (xFAIL_TAC: string -> xtactic) =
  fun tok g -> failwith tok;;

let (xALL_TAC:xtactic) =
  fun g -> null_meta,[g],fun _ [th] -> th;;

let xTRY tac =
  xORELSE tac xALL_TAC;;

let rec xREPEAT tac g =
  (xORELSE (xTHEN tac (xREPEAT tac)) xALL_TAC) g;;

let xEVERY tacl =
  itlist (fun t1 t2 -> xTHEN t1 t2) tacl xALL_TAC;;

let (xFIRST: xtactic list -> xtactic) =
  fun tacl g -> end_itlist (fun t1 t2 -> xORELSE t1 t2) tacl g;;

let xMAP_EVERY tacf lst =
  xEVERY (map tacf lst);;

let xMAP_FIRST tacf lst =
  xFIRST (map tacf lst);;

let (xCHANGED_TAC: xtactic -> xtactic) =
  fun tac g ->
    let (meta,gl,_ as gstate) = tac g in
    if meta = null_meta & length gl = 1 & equals_xgoal (hd gl) g
    then failwith "CHANGED_TAC" else gstate;;

let rec xREPLICATE_TAC n tac =
  if n <= 0 then xALL_TAC else xTHEN tac (xREPLICATE_TAC (n - 1) tac);;

(* ------------------------------------------------------------------------- *)
(* Combinators for theorem continuations adjusted for xthms and xtactics.    *)
(* ------------------------------------------------------------------------- *)

let ((xTHEN_TCL): xthm_tactical -> xthm_tactical -> xthm_tactical) =
  fun ttcl1 ttcl2 ttac -> ttcl1 (ttcl2 ttac);;

let ((xORELSE_TCL): xthm_tactical -> xthm_tactical -> xthm_tactical) =
  fun ttcl1 ttcl2 ttac th ->
    try ttcl1 ttac th with Failure _ -> ttcl2 ttac th;;

let rec xREPEAT_TCL ttcl ttac th =
  (xORELSE_TCL (xTHEN_TCL ttcl (xREPEAT_TCL ttcl)) I) ttac th;;

let (xREPEAT_GTCL: xthm_tactical -> xthm_tactical) =
  let rec xREPEAT_GTCL ttcl ttac th g =
    try ttcl (xREPEAT_GTCL ttcl ttac) th g with Failure _ -> ttac th g in
  xREPEAT_GTCL;;

let (xALL_THEN: xthm_tactical) =
  I;;

let (xNO_THEN: xthm_tactical) =
  fun ttac th -> failwith "NO_THEN";;

let xEVERY_TCL ttcll =
  itlist (fun t1 t2 -> xTHEN_TCL t1 t2) ttcll xALL_THEN;;

let xFIRST_TCL ttcll =
  end_itlist (fun t1 t2 -> xORELSE_TCL t1 t2) ttcll;;

(* ------------------------------------------------------------------------- *)
(* Tactics to augment assumption list. Note that to allow "ASSUME p" for     *)
(* any assumption "p", these add a PROVE_HYP in the justification function,  *)
(* just in case.                                                             *)
(* ------------------------------------------------------------------------- *)

let (xLABEL_TAC: string -> xthm_tactic) =
  fun s thm ((asl,w),id) ->
    let thm' = xthm_thm thm in
    null_meta,[(((s,thm')::asl,w),id)],
    fun i [th] -> PROVE_HYP (INSTANTIATE_ALL i thm') th;;

(* ------------------------------------------------------------------------- *)
(* Manipulation of assumption list.                                          *)
(* ------------------------------------------------------------------------- *)

let mk_asm_xthm th = mk_xthm0 "<asm>" th;;

let (xFIND_ASSUM: xthm_tactic -> term -> xtactic) =
  fun ttac t (((asl,w),id) as g) ->
    ttac (mk_asm_xthm (snd(find (fun (_,th) -> concl th = t) asl))) g;;

let (xPOP_ASSUM: xthm_tactic -> xtactic) =
  fun ttac ->
   function ((((_,th)::asl),w),id) -> ttac (mk_asm_xthm th) ((asl,w),id)
    | _ -> failwith "POP_ASSUM: No assumption to pop";;

let (xASSUM_LIST: (xthm list -> xtactic) -> xtactic) =
    fun aslfun ((asl,w),id) -> aslfun (map (mk_asm_xthm o snd) asl)
               ((asl,w),id);;

let (xPOP_ASSUM_LIST: (xthm list -> xtactic) -> xtactic) =
  fun asltac ((asl,w),id) -> asltac (map (mk_asm_xthm o snd) asl) (([],w),id);;

let (xEVERY_ASSUM: xthm_tactic -> xtactic) =
  fun ttac -> xASSUM_LIST (xMAP_EVERY ttac);;

let (xFIRST_ASSUM: xthm_tactic -> xtactic) =
  fun ttac (((asl,w),id) as g) ->
                    tryfind (fun (_,th) -> ttac (mk_asm_xthm th) g) asl;;

let (xRULE_ASSUM_TAC :(xthm->xthm)->xtactic) =
  fun rule ((asl,w),id) ->
              (xTHEN (xPOP_ASSUM_LIST(K xALL_TAC))
                     (xMAP_EVERY
                        (fun (s,th) -> xLABEL_TAC s (rule (mk_asm_xthm th)))
                        (rev asl)))
              ((asl,w),id);;

(* ------------------------------------------------------------------------- *)
(* Operate on assumption identified by a label.                              *)
(* ------------------------------------------------------------------------- *)

let (xUSE_THEN:string->xthm_tactic->xtactic) =
  fun s ttac (((asl,w),id) as gl) ->
    let th = try assoc s asl with Failure _ ->
             failwith("USE_TAC: didn't find assumption "^s) in
    ttac (mk_asm_xthm th) gl;;

let (xREMOVE_THEN:string->xthm_tactic->xtactic) =
  fun s ttac ((asl,w),id) ->
    let th = try assoc s asl with Failure _ ->
             failwith("USE_TAC: didn't find assumption "^s) in
    let asl1,asl2 = chop_list(index s (map fst asl)) asl in
    let asl' = asl1 @ tl asl2 in
    ttac (mk_asm_xthm th) ((asl',w),id);;

(* ------------------------------------------------------------------------- *)
(* General tool to augment a required set of theorems with assumptions.      *)
(* ------------------------------------------------------------------------- *)

let (xASM :(xthm list -> xtactic)->(xthm list -> xtactic)) =
  fun tltac ths
         (((asl,w),id) as g) -> tltac (map (mk_asm_xthm o snd) asl @ ths) g;;

(* ------------------------------------------------------------------------- *)
(* A printer for xgoals etc.                                                 *)
(* ------------------------------------------------------------------------- *)

let print_xgoal ((g,x):xgoal) : unit =
  print_goal g;;

let (print_xgoalstack:xgoalstack->unit) =
  let print_xgoalstate k gs =
    let (_,gl,_) = gs in
    let n = length gl in
    let s = if n = 0 then "No subgoals" else
              (string_of_int k)^" subgoal"^(if k > 1 then "s" else "")
           ^" ("^(string_of_int n)^" total)" in
    print_string s; print_newline();
    if gl = [] then () else
    do_list (print_xgoal o C el gl) (rev(0--(k-1))) in
  fun l ->
    if l = [] then print_string "Empty goalstack"
    else if tl l = [] then
      let (_,gl,_ as gs) = hd l in
      print_xgoalstate 1 gs
    else
      let (_,gl,_ as gs) = hd l
      and (_,gl0,_) = hd(tl l) in
      let p = length gl - length gl0 in
      let p' = if p < 1 then 1 else p + 1 in
      print_xgoalstate p' gs;;

(* ------------------------------------------------------------------------- *)
(* Convert an xtactic into an xrefinement.                                   *)
(* ------------------------------------------------------------------------- *)

let (xby:xtactic->xrefinement) =
  fun tac ((mvs,inst),gls,just) ->
    let g = hd gls
    and ogls = tl gls in
    let ((newmvs,newinst),subgls,subjust) = tac g in
    let n = length subgls in
    let mvs' = union newmvs mvs
    and inst' = compose_insts inst newinst
    and gls' = subgls @ map (inst_xgoal newinst) ogls in
    let just' i ths =
      let i' = compose_insts inst' i in
      let cths,oths = chop_list n ths in
      let sths = (subjust i cths) :: oths in
      just i' sths in
    (mvs',inst'),gls',just';;

(* ------------------------------------------------------------------------- *)
(* Rotate for xgoalstate.                                                    *)
(* ------------------------------------------------------------------------- *)

let (xrotate:int->xrefinement) =
  let rotate_p (meta,sgs,just) =
    let sgs' = (tl sgs)@[hd sgs] in
    let just' i ths =
      let ths' = (last ths)::(butlast ths) in
      just i ths' in
    (meta,sgs',just')
  and rotate_n (meta,sgs,just) =
    let sgs' = (last sgs)::(butlast sgs) in
    let just' i ths =
      let ths' = (tl ths)@[hd ths] in
      just i ths' in
    (meta,sgs',just') in
  fun n -> if n > 0 then funpow n rotate_p
           else funpow (-n) rotate_n;;

(* ------------------------------------------------------------------------- *)
(* Refinement proof, tactic proof etc for xgoals/xtactics.                   *)
(* ------------------------------------------------------------------------- *)

let (mk_xgoalstate:goal->xgoalstate) =
  fun (asl,w) ->
    if type_of w = bool_ty then
      let id = (inc_goal_id_counter (); !the_goal_id_counter) in
      null_meta,[((asl,w),id)],
      (fun inst [th] -> INSTANTIATE_ALL inst th)
    else failwith "mk_goalstate: Non-boolean goal";;

let (xTAC_PROOF : goal * xtactic -> thm) =
  fun (g,tac) ->
    let gstate = mk_xgoalstate g in
    let _,sgs,just = xby tac gstate in
    if sgs = [] then just null_inst []
    else failwith "TAC_PROOF: Unsolved goals";;

let xprove(t,tac) =
  let th = xTAC_PROOF(([],t),tac) in
  let t' = concl th in
  let th' =
    if t' = t then th else
    try EQ_MP (ALPHA t' t) th
    with Failure _ -> failwith "prove: justification generated wrong theorem" in
  mk_xthm (th', ("<tactic-proof>",[]))

(* ------------------------------------------------------------------------- *)
(* Subgoal package for xgoals.                                               *)
(* ------------------------------------------------------------------------- *)

let current_xgoalstack = ref ([] :xgoalstack);;

let (xrefine:xrefinement->xgoalstack) =
  fun r ->
    let l = !current_xgoalstack in
    let h = hd l in
    let res = r h :: l in
    current_xgoalstack := res;
    !current_xgoalstack;;

let flush_xgoalstack() =
  let l = !current_xgoalstack in
  current_xgoalstack := [hd l];;

let xe tac = xrefine(xby(xVALID tac));;

let xr n = xrefine(xrotate n);;

let xset_goal(asl,w) =
  current_xgoalstack :=
    [mk_xgoalstate(map (fun t -> "",ASSUME t) asl,w)];
  !current_xgoalstack;;

let xg t =
  let fvs = sort (<) (map (fst o dest_var) (frees t)) in
  (if fvs <> [] then
     let errmsg = end_itlist (fun s t -> s^", "^t) fvs in
     warn true ("Free variables in goal: "^errmsg)
   else ());
   xset_goal([],t);;

let xb() =
  let l = !current_xgoalstack in
  if length l = 1 then failwith "Can't back up any more" else
  current_xgoalstack := tl l;
  !current_xgoalstack;;

let xp() =
  !current_xgoalstack;;

let xtop_realgoal() =
  let (_,(((asl,w),_)::_),_)::_ = !current_xgoalstack in
  asl,w;;

let xtop_goal() =
  let asl,w = xtop_realgoal() in
  map (concl o snd) asl,w;;

let xtop_thm() =
  let (_,[],f)::_ = !current_xgoalstack in
  mk_xthm (f null_inst [], ("<tactic-proof>",[]));;

(* ------------------------------------------------------------------------- *)
(* Install the goal-related printers.                                        *)
(* ------------------------------------------------------------------------- *)

#install_printer print_xgoal;;
#install_printer print_xgoalstack;;
