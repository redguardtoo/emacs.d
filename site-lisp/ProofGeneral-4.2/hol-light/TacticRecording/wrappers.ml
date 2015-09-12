(* ========================================================================== *)
(* WRAPPER FUNCTIONS (HOL LIGHT)                                              *)
(* - Functions for promoting thm/goal-related ML objects for xthm/xgoal       *)
(*                                                                            *)
(* By Mark Adams                                                              *)
(* Copyright (c) Univeristy of Edinburgh, 2011-2012                           *)
(* ========================================================================== *)



(* ** THEOREM-RELATED WRAPPER FUNCTIONS ** *)


(* mldata_as_meta_arg *)

let mldata_as_meta_arg (obj:mldata) =
  match obj with
    (x, ((_::_) as args))
       -> Mlfn (x, front args)
  | _  -> failwith "mldata_as_meta_arg: Unexpected empty rule arg list";;

let mldata_as_meta2_arg (obj:mldata) =
  match obj with
    (x, ((_::_) as args))
       -> Mlfn (x, (front o front) args)
  | _  -> failwith "mldata_as_meta_arg: Unexpected empty rule arg list";;


(* detect_rule_app *)

(* Based on the assumption that the given meta function actually executes its *)
(* rule argument at some point, this utility detects such an execution during *)
(* the demotion of a given xrule argument to a rule.  The meta function's     *)
(* result is returned along with an 'farg' that captures the rule.            *)

let detect_rule_app (mfunc:('a->thm)->'b) (xr:'a->xthm) : 'c =
  let temp = ref (Mlfn ("<rule>", []) : mlarg) in
  let r arg = let xth = xr arg in
              let (th,obj) = dest_xthm xth in
              (temp := mldata_as_meta_arg obj;
               th) in
  let th = mfunc r in
  (th,!temp);;

let detect_metarule_app (mfunc:(('a->thm)->'b->thm)->'c)
                        (xmr:('a->xthm)->'b->xthm) : 'd =
  let temp = ref (Mlfn ("<meta-rule>",[]) : mlarg) in
  let mr marg arg = let xmarg arg0 =
                       let th = marg arg0 in
                       let obj = ("<rule>", [Mlfn ("<arg>",[])]) in
                       mk_xthm (th,obj) in
                    let xth = xmr xmarg arg in
                    let (th,obj) = dest_xthm xth in
                    (temp := mldata_as_meta2_arg obj;
                     th) in
  let th = mfunc mr in
  (th,!temp);;


(* Theorem wrapper *)

let theorem_wrap (x:string) (th:thm) : xthm =
  (th, (x,[]));;


(* Rule wrappers *)

(* Lots of rule wrappers are required because there are many different type   *)
(* shapes for rules.                                                          *)

let rule_wrap0 obj (r:'a->thm) (arg:'a) : xthm =
  let th' = r arg in
  mk_xthm (th',obj);;

let conv_wrap x (r:term->thm) (tm:term) : xthm =
  rule_wrap0 (x, [Mlterm tm]) r tm;;

let thm_conv_wrap x (r:thm->term->thm) (xth:xthm) tm : xthm =
  let (th,prf) = dest_xthm xth in
  rule_wrap0 (x, [Mlthm prf; Mlterm tm]) (r th) tm;;

let thmlist_conv_wrap x (r:thm list->term->thm) xths (tm:term) : xthm =
  let (ths,prfs) = unzip (map dest_xthm xths) in
  rule_wrap0 (x, [Mllist (map (fun prf -> Mlthm prf) prfs); Mlterm tm])
             (r ths) tm;;

let rule_wrap x (r:thm->thm) (xth:xthm) : xthm =
  let (th,prf) = dest_xthm xth in
  rule_wrap0 (x, [Mlthm prf]) r th;;

let drule_wrap x (r:thm->thm->thm) (xth1:xthm) (xth2:xthm) : xthm =
  let (th1,prf1) = dest_xthm xth1 in
  let (th2,prf2) = dest_xthm xth2 in
  rule_wrap0 (x, [Mlthm prf1; Mlthm prf2]) (r th1) th2;;

let prule_wrap x (r:thm*thm->thm) ((xth1:xthm),(xth2:xthm)) : xthm =
  let (th1,prf1) = dest_xthm xth1 in
  let (th2,prf2) = dest_xthm xth2 in
  rule_wrap0 (x, [Mlpair(Mlthm prf1, Mlthm prf2)]) r (th1,th2);;

let trule_wrap x (r:thm->thm->thm->thm)
                 (xth1:xthm) (xth2:xthm) (xth3:xthm) : xthm =
  let (th1,prf1) = dest_xthm xth1 in
  let (th2,prf2) = dest_xthm xth2 in
  let (th3,prf3) = dest_xthm xth3 in
  rule_wrap0 (x, [Mlthm prf1; Mlthm prf2; Mlthm prf3]) (r th1 th2) th3;;

let term_rule_wrap x (r:term->thm->thm) tm (xth:xthm) : xthm =
  let (th,prf) = dest_xthm xth in
  rule_wrap0 (x, [Mlterm tm; Mlthm prf]) (r tm) th;;

let termpair_rule_wrap x (r:term*term->thm->thm) (tm1,tm2) (xth:xthm) : xthm =
  let (th,prf) = dest_xthm xth in
  rule_wrap0 (x, [Mlpair(Mlterm tm1,Mlterm tm2); Mlthm prf]) (r (tm1,tm2)) th;;

let termthmpair_rule_wrap x (r:term*thm->thm->thm) (tm,xth0) (xth:xthm) : xthm =
  let (th0,prf0) = dest_xthm xth0 in
  let (th,prf) = dest_xthm xth in
  rule_wrap0 (x, [Mlpair(Mlterm tm, Mlthm prf0); Mlthm prf]) (r (tm,th0)) th;;

let termlist_rule_wrap x (r:term list->thm->thm) tms (xth:xthm) : xthm =
  let (th,prf) = dest_xthm xth in
  rule_wrap0 (x, [Mllist (map (fun tm -> Mlterm tm) tms); Mlthm prf])
             (r tms) th;;

let terminst_rule_wrap x (r:(term*term)list->thm->thm) theta (xth:xthm) : xthm =
  let (th,prf) = dest_xthm xth in
  rule_wrap0 (x,
              [Mllist (map (fun (tm1,tm2) -> Mlpair(Mlterm tm1, Mlterm tm2))
                           theta);
               Mlthm prf])
             (r theta) th;;

let typeinst_rule_wrap x (r:(hol_type*hol_type)list->thm->thm)
                         theta (xth:xthm) : xthm =
  let (th,prf) = dest_xthm xth in
  rule_wrap0 (x,
              [Mllist (map (fun (tm1,tm2) -> Mlpair(Mltype tm1, Mltype tm2))
                           theta);
               Mlthm prf])
             (r theta) th;;

let thmlist_rule_wrap x (r:thm list->thm->thm) xths (xth:xthm) : xthm =
  let (ths,prfs) = unzip (map dest_xthm xths) in
  let (th,prf) = dest_xthm xth in
  rule_wrap0 (x, [Mllist (map (fun prf -> Mlthm prf) prfs); Mlthm prf])
             (r ths) th;;


(* Multi-rule wrappers *)

let multirule_wrap0 obj (r:'a->thm list) (arg:'a) : xthm list =
  let ths' = r arg in
  let n = length ths' in
  let infos' = map (fun i -> ("el", [Mlint i; Mlfn obj])) (0 -- (n-1)) in
  map mk_xthm (zip ths' infos');; 

let multirule_wrap x (r:thm->thm list) (xth:xthm) : xthm list =
  let (th,prf) = dest_xthm xth in
  multirule_wrap0 (x, [Mlthm prf]) r th;;


(* Meta rule wrappers *)

let meta_rule_wrap0 info0 (mr:('a->thm)->'b->thm)
                          (xr:'a->xthm) (arg:'b) : xthm =
  let (th',f) = detect_rule_app (fun r -> mr r arg) xr in
  let (x,args0) = info0 in
  let obj' = (x, f::args0) in
  (th',obj');;

let conv_conv_wrap x (mc:conv->conv) (xc:term->xthm) (tm:term) : xthm =
  meta_rule_wrap0 (x, [Mlterm tm]) mc xc tm;;



(* ** TACTIC-RELATED WRAPPER FUNCTIONS ** *)

(* These functions are for promoting existing tactics and tacticals.          *)


(* Generic basic wrapper util *)

(* Applies a tactic and incorproates the results into the goal tree.  Takes   *)
(* an "infotactic", i.e. like a normal tactic that works on 'goal' and        *)
(* returns 'goalstate', but that also returns a 'gstep' summary of the        *)
(* operation.  This is used to promote every basic tactic-based function.     *)

let infotactic_wrap (infotac:goal->goalstate*mldata) (xg:xgoal) : xgoalstate =
  let (g,id) = dest_xgoal xg in
  let ((meta,gs,just),obj) = infotac g in
  let xgs = extend_gtree id (Gatom obj) gs in
  (meta,xgs,just);;


(* Generic box wrapper util *)

(* Sets up a box to apply an xtactic within, applies the xtactic (which       *)
(* incorporates itself into the goal tree) and wires up the resulting         *)
(* subgoals to external subgoals of the box.  Note that this is not quite     *)
(* generic enough for 'SUBGOAL_THEN' (because there is not a total surjection *)
(* between internal and external goals).                                      *)

let infobox_wrap (xinfotac:xgoal->xgoalstate*label) (xg:xgoal) : xgoalstate =
  let (g,id) = dest_xgoal xg in
  let (id0,gtr0) = new_active_subgtree id g in
  let xg0 = mk_xgoal (g,id0) in
  let ((meta,xgs0,just),l) = xinfotac xg0 in
  let (gs0,ids0) = unzip (map dest_xgoal xgs0) in
  let xgs = extend_gtree id (Gbox (l,gtr0,false)) gs0 in
  let ids = map xgoal_id xgs in
  (do_list externalise_gtree (zip ids0 ids);
   (meta,xgs,just));;


(* Tactic wrapper *)

(* This is for wrapping around a tactic, to promote it to work on xgoals and  *)
(* incorporate the results into an existing gtree.                            *)

let tactic_wrap0 obj (tac:tactic) : xtactic =
  let infotac g = (tac g, obj) in
  infotactic_wrap infotac;;

let tactic_wrap x tac =
  tactic_wrap0 (x, []) tac;;

let string_tactic_wrap x (tac:string->tactic) (s:string) : xtactic =
  tactic_wrap0 (x, [Mlstring s]) (tac s);;

let term_tactic_wrap x (tac:term->tactic) (tm:term) : xtactic =
  tactic_wrap0 (x, [Mlterm tm]) (tac tm);;

let termpair_tactic_wrap x (tac:term*term->tactic) (tm1,tm2) : xtactic =
  tactic_wrap0 (x, [Mlpair (Mlterm tm1, Mlterm tm2)]) (tac (tm1,tm2));;

let termlist_tactic_wrap x (tac:term list->tactic) tms : xtactic =
  tactic_wrap0 (x, [Mllist (map (fun tm -> Mlterm tm) tms)]) (tac tms);;

let thm_tactic_wrap x (tac:thm->tactic) (xth:xthm) : xtactic =
  let (th,prf) = dest_xthm xth in
  tactic_wrap0 (x, [Mlthm prf]) (tac th);;

let thmlist_tactic_wrap x (tac:thm list->tactic) (xths:xthm list) : xtactic =
  let (ths,prfs) = unzip (map dest_xthm xths) in
  tactic_wrap0 (x, [Mllist (map (fun prf -> Mlthm prf) prfs)]) (tac ths);;

let stringthm_tactic_wrap x (tac:string->thm->tactic) s (xth:xthm) : xtactic =
  let (th,prf) = dest_xthm xth in
  tactic_wrap0 (x, [Mlstring s; Mlthm prf]) (tac s th);;


(* Meta-tactic wrapper *)

(* For tactics that take rule arguments.                                      *)

let meta_tactic_wrap0 info0 (mtac:('a->thm)->tactic)
                            (xr:'a->xthm) : xtactic =
  let infotac g =
     let (gst,f) = detect_rule_app (fun r -> mtac r g) xr in
     let (x,args0) = info0 in
     let obj = (x, f::args0) in
     (gst,obj) in
  infotactic_wrap infotac;;

let conv_tactic_wrap x (mtac:conv->tactic) (xc:xconv) : xtactic =
  meta_tactic_wrap0 (x, []) mtac xc;;

let metameta_tactic_wrap info0 (mmtac:(('a->thm)->'b->thm)->tactic)
                               (xmr:('a->xthm)->'b->xthm) : xtactic =
  let infotac g =
     let (gst,f) = detect_metarule_app (fun mr -> mmtac mr g) xmr in
     let (x,args0) = info0 in
     let obj = (x, f::args0) in
     (gst,obj) in
  infotactic_wrap infotac;;

let convconvthmlist_tactic_wrap x (mmtac:(conv->conv)->thm list->tactic)
                                 (xmc:xconv->xconv) (xths:xthm list) : xtactic =
  let (ths,prfs) = unzip (map dest_xthm xths) in
  metameta_tactic_wrap (x, [Mllist (map (fun prf -> Mlthm prf) prfs)])
                       (fun mc -> mmtac mc ths)
                       xmc;;


(* Tactical wrapper *)

(* This is for wrapping around a tactical, to incorporate the results into a  *)
(* box in an existing gtree, where the execution of the tactical's tactics is *)
(* captured inside the box, so that they can be stepped through and/or        *)
(* refactored.  Thus we cannot take the tactical as a black box; it must      *)
(* already be promoted to work with xtactics and xgoals.  This must done by   *)
(* hand for each tactical by trivially adjusting its original source code.    *)

let tactical_wrap0 obj (xttcl:'a->xtactic) (arg:'a) : xtactic =
  let xinfotac xg = (xttcl arg xg, Tactical obj) in
  infobox_wrap xinfotac;;

let tactical_wrap x (xttcl:'a->xtactic) (xtac:'a) : xtactic =
  tactical_wrap0 (x,[]) xttcl xtac;;

let btactical_wrap x (xttcl:'a->'b->xtactic) (xtac1:'a) (xtac2:'b) : xtactic =
  tactical_wrap0 (x,[]) (xttcl xtac1) xtac2;;

let int_tactical_wrap x (xttcl:int->'a->xtactic) (n:int) (xtac:'a) : xtactic =
  tactical_wrap0 (x, [Mlint n]) (xttcl n) xtac;;

let list_tactical_wrap x (xttcl:('a->xtactic)->'a list->xtactic)
                         (xtac:'a->xtactic) (l:'a list) : xtactic =
  tactical_wrap0 (x,[]) (xttcl xtac) l;;


(* HILABEL *)

(* Command for putting the result of a tactic into a box and giving the box a *)
(* label (distinct from a tactical label).                                    *)

let HILABEL x (xtac:xtactic) : xtactic =
  let xinfotac xg = (xtac xg, Label x) in
  infobox_wrap xinfotac;;


(* xSUBGOAL_THEN - seems to be a special case *)

let xASSUME = conv_wrap "ASSUME" ASSUME;;

let xSUBGOAL_THEN (tm:term) (ttac:xthm_tactic) (xg:xgoal) : xgoalstate =
  let arg = xASSUME tm in

  let (g,id) = dest_xgoal xg in
  let (id0,gtr0) = new_active_subgtree id g in
  let xg0 = mk_xgoal (g,id0) in
  let (meta,xgs0,just) = ttac arg xg0 in

  let (asl,_) = g in
  let g2 = (asl,tm) in
  let obj = ("SUBGOAL_THEN",
               [Mlterm tm; (mldata_as_meta_arg o gtree_tactic) gtr0]) in

  let (gs0,ids0) = unzip (map dest_xgoal xgs0) in
  let xgs = extend_gtree id (Gbox (Tactical obj, gtr0, true)) (g2::gs0) in
  let ids1 = map xgoal_id (tl xgs) in
  let just' = fun i l -> PROVE_HYP (hd l) (just i (tl l)) in
  (do_list externalise_gtree (zip ids0 ids1);
   (meta,xgs,just'));;


(*
let SUBGOAL_TAC s tm prfs =
  match prfs with
   p::ps -> (warn (ps <> []) "SUBGOAL_TAC: additional subproofs ignored";
             SUBGOAL_THEN tm (LABEL_TAC s) THENL [p; ALL_TAC])
  | [] -> failwith "SUBGOAL_TAC: no subproof given";;

let (FREEZE_THEN :thm_tactical) =
  fun ttac th (asl,w) ->
    let meta,gl,just = ttac (ASSUME(concl th)) (asl,w) in
    meta,gl,fun i l -> PROVE_HYP th (just i l);;
*)
