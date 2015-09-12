(* ========================================================================= *)
(* HOL Light subgoal package amended for Proof General and Prooftree.        *)
(*                                                                           *)
(* Mark Adams, David Aspinall.						     *)
(* LFCS, School of Informatics, University of Edinburgh			     *)
(*                                                                           *)
(* (c) Copyright University of Edinburgh and authors, 2012.                  *)
(*									     *)
(* This file contains some functions that are modified from the		     *)
(* original HOL Light code, and is therefore subject to the HOL Light	     *)
(* copyright, see the file LICENSE-HOL-LIGHT in this directory.		     *)
(*									     *)
(* ========================================================================= *)
(*									     *)
(* This file overwrites HOL Light's subgoal package commands with variants   *)
(* that output additional annotations specifically for Prooftree.  These get *)
(* intercepted by Proof General, which removes them from the output          *)
(* displayed to the Proof General user.					     *)

(* TODO: 
   1. add urgent message annotations for errors and strings output during
      long-running tactics
   2. fix on/off: don't turn off prompt annotation, support Prooftree on/off.
*)

(* ------------------------------------------------------------------------- *)
(* Goal counter for providing goal ids.                                      *)
(* ------------------------------------------------------------------------- *)

type goal_id = int;;

let string_of_goal_id id = string_of_int id;;

let the_goal_counter = ref (0 : goal_id);;

let inc_goal_counter () =
  (the_goal_counter := !the_goal_counter + 1);;

let reset_goal_counter () =
  (the_goal_counter := 0;
   !the_goal_counter);;

(* ------------------------------------------------------------------------- *)
(* An xgoal extends a goal with an identity.                                 *)
(* ------------------------------------------------------------------------- *)

type xgoal = goal * goal_id;;

let dest_xgoal (gx : xgoal) = gx;;

(* ------------------------------------------------------------------------- *)
(* The xgoalstate is like goalstate but for xgoals instead of goals.         *)
(* ------------------------------------------------------------------------- *)

type xgoalstate = (term list * instantiation) * xgoal list * justification;;

(* ------------------------------------------------------------------------- *)
(* A goalstack but for xgoals.  Overwrites original HL datatype.             *)
(* ------------------------------------------------------------------------- *)

type goalstack = xgoalstate list;;

(* ------------------------------------------------------------------------- *)
(* A refinement but for xgoals.                                              *)
(* ------------------------------------------------------------------------- *)

type xrefinement = xgoalstate -> xgoalstate;;

(* ------------------------------------------------------------------------- *)
(* Instantiation of xgoals.                                                  *)
(* ------------------------------------------------------------------------- *)

let (inst_xgoal:instantiation->xgoal->xgoal) =
  fun p ((thms,w),id) ->
    (map (I F_F INSTANTIATE_ALL p) thms,instantiate p w),id;;

(* ------------------------------------------------------------------------- *)
(* A printer for xgoals and xgoalstacks.                                     *)
(* ------------------------------------------------------------------------- *)

let the_new_goal_ids = ref ([] : goal_id list);;

let the_tactic_flag = ref false;;

let print_string_seplist sep xs =
  if (xs = [])
    then ()
    else (print_string (hd xs);
          do_list (fun x -> print_string sep; print_string x) (tl xs));;

let print_xgoal ((g,id) : xgoal) : unit =
  ((if (!pg_mode)
      then (print_string ("[Goal ID " ^ string_of_goal_id id ^ "]");
            print_newline ()));
   print_goal g);;

let (print_xgoalstack:goalstack->unit) =
  let print_xgoalstate k gs =
    let (_,gl,_) = gs in
    let n = length gl in
    let s = if n = 0 then "No subgoals" else
              (string_of_int k)^" subgoal"^(if k > 1 then "s" else "")
           ^" ("^(string_of_int n)^" total)" in
    print_string s; print_newline();
    if gl = [] then () else
    (do_list (print_xgoal o C el gl) (rev(1--(k-1)));
     (if (!pg_mode) then print_string "[*]");
     print_xgoal (el 0 gl)) in
  fun l ->
   ((if (!pg_mode) & (!the_tactic_flag)
       then let xs = map string_of_int (!the_new_goal_ids) in
            (the_tactic_flag := false;
             print_string  "[New Goal IDs: ";
             print_string_seplist " " xs;
             print_string "]";
             print_newline ()));
    (if l = [] then print_string "Empty goalstack"
     else if tl l = [] then
       let (_,gl,_ as gs) = hd l in
       print_xgoalstate 1 gs
     else
       let (_,gl,_ as gs) = hd l
       and (_,gl0,_) = hd(tl l) in
       let p = length gl - length gl0 in
       let p' = if p < 1 then 1 else p + 1 in
       print_xgoalstate p' gs);
    (if (!pg_mode) then
     let (vs,theta) =
        if (l = []) then ([],[])
                    else let ((vs,(_,theta,_)),_,_) = hd l in
                         (vs,theta) in
     let foo v =
        let (x,_) = dest_var v in
        "?" (* FIXME: Coq syntax for meta vars is expected by Prooftree *)
        ^ x ^ if (can (rev_assoc v) theta) then " using" else " open" in
     let xs = map foo vs in
     (print_newline();
      print_string "(dependent evars:";
      if xs != [] then 
       (print_string " ";
	print_string_seplist ", " xs;
	print_string ",");
      print_string ")";
      print_newline ())));;

(* ------------------------------------------------------------------------- *)
(* Goal labelling, for fresh xgoals.                                         *)
(* ------------------------------------------------------------------------- *)

let label_goals (gs : goal list) : xgoal list =
  let gxs = map (fun g -> inc_goal_counter (); (g, !the_goal_counter))
                gs in
  (the_new_goal_ids := map snd gxs;
   gxs);;

(* ------------------------------------------------------------------------- *)
(* Version of 'by' for xrefinements.                                         *)
(* ------------------------------------------------------------------------- *)

let (xby:tactic->xrefinement) =
  fun tac ((mvs,inst),glsx,just) ->
    let gx = hd glsx
    and oglsx = tl glsx in
    let (g,id) = dest_xgoal gx in
    let ((newmvs,newinst),subgls,subjust) = tac g in
    let subglsx = label_goals subgls in
    let n = length subglsx in
    let mvs' = union newmvs mvs
    and inst' = compose_insts inst newinst
    and glsx' = subglsx @ map (inst_xgoal newinst) oglsx in
    let just' i ths =
      let i' = compose_insts inst' i in
      let cths,oths = chop_list n ths in
      let sths = (subjust i cths) :: oths in
      just i' sths in
    (mvs',inst'),glsx',just';;

(* ------------------------------------------------------------------------- *)
(* Rotate but for xgoalstate.  Only change is different ML datatype.         *)
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
(* Perform refinement proof, tactic proof etc.                               *)
(* ------------------------------------------------------------------------- *)

let (mk_xgoalstate:goal->xgoalstate) =
  fun (asl,w) ->
    if type_of w = bool_ty then
      null_meta,[((asl,w), reset_goal_counter ())],
      (fun inst [th] -> INSTANTIATE_ALL inst th)
    else failwith "mk_goalstate: Non-boolean goal";;

(* ------------------------------------------------------------------------- *)
(* The global state counts the total number of proof steps taken.            *)
(* ------------------------------------------------------------------------- *)

let the_pg_global_state = ref 1;;

let inc_pg_global_state () =
  (the_pg_global_state := !the_pg_global_state + 1);;

let dec_pg_global_state n =
  (the_pg_global_state := !the_pg_global_state - n);;

let pg_global_state () = !the_pg_global_state;;

(* ------------------------------------------------------------------------- *)
(* The proof state number is the length of the current goal stack.           *)
(* ------------------------------------------------------------------------- *)

let the_current_xgoalstack = ref ([] : goalstack);;

let pg_proof_state () = length !the_current_xgoalstack;;

(* ------------------------------------------------------------------------- *)
(* Subgoal package for xgoals and with a constrained undo protocol for       *)
(* interacting with Proof General to track the state.  These overwrite the   *)
(* existing commands and may cause breakage of interactive proofs.           *)
(*								             *)
(* The restrictions are:						     *)
(*  - top_thm may only be called once and closes the currently open proof.   *)
(*  - the back command b() is not allowed to appear in a file.		     *)
(*								             *)
(* ------------------------------------------------------------------------- *)

let (xrefine:xrefinement->goalstack) =
  fun r ->
    let l = !the_current_xgoalstack in
    let h = hd l in
    let res = r h :: l in
    the_current_xgoalstack := res;
    !the_current_xgoalstack;;

let flush_goalstack() =
  let l = !the_current_xgoalstack in
  the_current_xgoalstack := [hd l];;

let e tac =
  let result = xrefine(xby(VALID tac)) in
  (inc_pg_global_state ();
   the_tactic_flag := true;
   result);;

let r n =
  (inc_pg_global_state ();
   xrefine(xrotate n));;

let set_goal(asl,w) =
  let aths = map ASSUME asl in
  (inc_pg_global_state ();
   the_current_xgoalstack :=
     [mk_xgoalstate(map (fun th -> "",th) aths,w)];
   !the_current_xgoalstack);;

let g t =
  let fvs = sort (<) (map (fst o dest_var) (frees t)) in
  (if fvs <> [] then
     let errmsg = end_itlist (fun s t -> s^", "^t) fvs in
     warn true ("Free variables in goal: "^errmsg)
   else ());
  set_goal([],t);;

let p() = !the_current_xgoalstack;;

let b() =
  failwith "Undo with b() is not available in Proof General top level";;

let top_realgoal() =
  let (_,(((asl,w),id)::_),_)::_ = !the_current_xgoalstack in
  asl,w;;

let top_goal() =
  let asl,w = top_realgoal() in
  map (concl o snd) asl,w;;

let plain_top_thm() =
  let (_,[],f)::_ = !the_current_xgoalstack in
   f null_inst [];;

let top_thm() = 
  let t = plain_top_thm() in
  (inc_pg_global_state();
   the_current_xgoalstack := [];
   t);;

(* ------------------------------------------------------------------------- *)
(* Undo handling functions for Proof General		                     *)
(* ------------------------------------------------------------------------- *)

let pg_undo n =
  let l = !the_current_xgoalstack in
   if length l < n then failwith "pg_undo: called with too many steps"
   else (dec_pg_global_state n;
         the_current_xgoalstack := snd (chop_list n l);
         p());;

let pg_kill() = 
  let n = length (!the_current_xgoalstack) in
  (dec_pg_global_state n;
   the_current_xgoalstack := [];
   print_string "*** Proof aborted.\n");;

let pg_forget s = 
   print_string ("*** Remove theorem "^s^"\n");;

let pg_restart() = 
   print_string "*** Session restarted.\n";;

(* ------------------------------------------------------------------------- *)
(* Configure the annotated prompt.				             *)
(* ------------------------------------------------------------------------- *)

pg_prompt_info := 
   fun () -> 
   let pst = pg_proof_state () and gst = pg_global_state () in
   string_of_int gst ^ "|" ^ string_of_int pst;;

(* ------------------------------------------------------------------------- *)
(* Printing the goal of a given Prooftree goal id.                           *)
(* ------------------------------------------------------------------------- *)

let print_xgoal_of_id (id:goal_id) : unit =
  let gsts = !the_current_xgoalstack in
  let find_goal (_,xgs,_) = find (fun (g,id0) -> id0 = id) xgs in
  let xg = tryfind find_goal gsts in
  print_xgoal xg;;

(* ------------------------------------------------------------------------- *)
(* Install the new goal-related printers.                                    *)
(* ------------------------------------------------------------------------- *)

#install_printer print_xgoal;;
#install_printer print_xgoalstack;;
