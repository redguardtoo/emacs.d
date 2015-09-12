(* ========================================================================= *)
(* HOL Light subgoal package amended for Proof General's Prooftree.          *)
(*                                                                           *)
(*       Mark Adams, School of Informatics, University of Edinburgh          *)
(*                                                                           *)
(* (c) Copyright, University of Edinburgh, 2012                              *)
(* ========================================================================= *)

(* This file provides alternatives to HOL Light's subgoal package commands   *)
(* that output additional annotations specifically for Prooftree.  These     *)
(* annotations get intercepted by Proof General, which removes them from the *)
(* output displayed to the Proof General user.  Annotation can be switched   *)
(* off completely with the 'pg_mode_off' command.                            *)

(* Note that this assumes the existence of xgoals (see 'xtactics.ml').       *)

(* ------------------------------------------------------------------------- *)
(* Proof General mode, for providing extra annotations for Prooftree.        *)
(* ------------------------------------------------------------------------- *)

let pg_mode = ref (false : bool);;

let pg_mode_on () = (pg_mode := true);;
let pg_mode_off () = (pg_mode := false);;

let get_pg_mode () = !pg_mode;;

(* ------------------------------------------------------------------------- *)
(* The Prooftree global state is an ever increasing counter.                 *)
(* ------------------------------------------------------------------------- *)

let the_pt_global_state = ref 1;;

let inc_pt_global_state () =
  (the_pt_global_state := !the_pt_global_state + 1);;

let pt_global_state () = !the_pt_global_state;;

(* ------------------------------------------------------------------------- *)
(* The Prooftree proof state is the length of the goal stack.                *)
(* ------------------------------------------------------------------------- *)

let pt_proof_state () = length !current_xgoalstack;;

let pt_back_to_proof_state n : xgoalstack =
  let pst = pt_proof_state () in
  if (0 <= n) & (n <= pst)
    then (current_xgoalstack :=
               snd (chop_list (pst-n) !current_xgoalstack);
          !current_xgoalstack)
    else failwith "Not a valid Prooftree state number";;

(* ------------------------------------------------------------------------- *)
(* Subgoal package commands adjusted to update Prooftree global state.       *)
(* ------------------------------------------------------------------------- *)

let the_tactic_flag = ref false;;

let xe tac =
  let result = xe tac in
  (inc_pt_global_state ();
   the_tactic_flag := true;      (* So that special info gets displayed *)
   result);;

let xr n =
  let result = xr n in
  (inc_pt_global_state ();
   result);;

let xset_goal (asl,w) =
  let result = xset_goal (asl,w) in
  (inc_pt_global_state ();
   result);;

let xg t =
  let fvs = sort (<) (map (fst o dest_var) (frees t)) in
  (if fvs <> [] then
     let errmsg = end_itlist (fun s t -> s^", "^t) fvs in
     warn true ("Free variables in goal: "^errmsg)
   else ());
   xset_goal([],t);;

let xb () =
  let result = xb () in
  (inc_pt_global_state ();
   result);;

(* ------------------------------------------------------------------------- *)
(* Special Prooftree printers for xgoals and xgoalstacks.                    *)
(* ------------------------------------------------------------------------- *)

let the_new_goal_ids = ref ([] : goalid list);;

let print_prooftree_xgoal ((g,id) : xgoal) : unit =
  ((if (!pg_mode)
      then (print_string ("[Goal ID " ^ string_of_goal_id id ^ "]");
            print_newline ()));
   print_goal g);;

let (print_prooftree_xgoalstack:xgoalstack->unit) =
  let print_prooftree_xgoalstate k gs =
    let (_,gl,_) = gs in
    let n = length gl in
    let s = if n = 0 then "No subgoals" else
              (string_of_int k)^" subgoal"^(if k > 1 then "s" else "")
           ^" ("^(string_of_int n)^" total)" in
    print_string s; print_newline();
    if gl = [] then () else
    (do_list (print_prooftree_xgoal o C el gl) (rev(1--(k-1)));
     (if (!pg_mode) then print_string "[*]");
     print_prooftree_xgoal (el 0 gl)) in
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
       print_prooftree_xgoalstate 1 gs
     else
       let (_,gl,_ as gs) = hd l
       and (_,gl0,_) = hd(tl l) in
       let p = length gl - length gl0 in
       let p' = if p < 1 then 1 else p + 1 in
       print_prooftree_xgoalstate p' gs);
    (if (!pg_mode) then
     let (vs,theta) =
        if (l = []) then ([],[])
                    else let ((vs,(_,theta,_)),_,_) = hd l in
                         (vs,theta) in
     let foo v =
        let (x,_) = dest_var v in
        x ^ if (can (rev_assoc v) theta) then " using" else " open" in
     let xs = map foo vs in
     (print_newline();
      print_string "(dependent evars: ";
      print_string_seplist ", " xs;
      print_string ")";
      print_newline ())));;

(* ------------------------------------------------------------------------- *)
(* Adjust the OCaml prompt to carry information for Prooftree.               *)
(* ------------------------------------------------------------------------- *)

let original_prompt_fn = !Toploop.read_interactive_input in
Toploop.read_interactive_input :=
   fun prompt buffer len ->
      let basic_prompt = "<" in        (* 'prompt' arg is ignored  *)
      let prompt' =
         if (!pg_mode)
           then let pst = pt_proof_state () and gst = pt_global_state () in
                "<prompt> " ^ basic_prompt ^ " " ^
                string_of_int gst ^ " || " ^ string_of_int pst ^
                " " ^ basic_prompt ^ " </prompt>"
           else prompt in
      original_prompt_fn prompt' buffer len;;

(* ------------------------------------------------------------------------- *)
(* Printing the goal of a given Prooftree goal id.                           *)
(* ------------------------------------------------------------------------- *)

let xgoal_of_id (id:goalid) : xgoal =
  let gsts = !current_xgoalstack in
  let find_goal (_,xgs,_) = find (fun (g,id0) -> id0 = id) xgs in
  let xg = tryfind find_goal gsts in
  xg;;

(* ------------------------------------------------------------------------- *)
(* Install the new goal-related printers.                                    *)
(* ------------------------------------------------------------------------- *)

#install_printer print_prooftree_xgoal;;
#install_printer print_prooftree_xgoalstack;;
