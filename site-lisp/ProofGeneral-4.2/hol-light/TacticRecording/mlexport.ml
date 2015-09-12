(* ========================================================================== *)
(* ML EXPORT (HOL LIGHT)                                                      *)
(* - Exporting recorded tactics into a proof script                           *)
(*                                                                            *)
(* By Mark Adams                                                              *)
(* Copyright (c) Univeristy of Edinburgh, 2012                                *)
(* ========================================================================== *)


(* Routines for exporting an ML tactic proof script from the recorded tactic  *)
(* proof tree, via a hiproof representation.                                  *)



(* ** UTILS ** *)


(* Printer for tactic is just the ML data printer *)

let print_tactic br obj = print_mldata br obj;;


(* Printer for subgoal comments *)

let print_hicomment_line ns =
  (print_string "(* *** Subgoal ";
   print_int (hd ns);
   do_list (fun n -> print_string "."; print_int n) (tl ns);
   print_string " *** *)\n");;


(* print_tactic_line *)

let print_tactic_line_with pr arg =
  (print_string "e ("; pr false arg; print_string ");;\n");;

let print_tactic_line obj =
  (print_tactic_line_with print_tactic obj);;

let print_hitrace_line_with fl pr htr =
  match htr with
    Hicomment ns -> if fl then print_hicomment_line ns
  | Hiproof h    -> print_tactic_line_with pr h;;


(* print_hiproof0 *)

(* This is a utility used in exporters, for basic cases not explicitly dealt  *)
(* with in the exporter's special cases.  Does not print tacticals, other     *)
(* than 'THEN' (for single arity) and 'THENL' (for multi-arity).  Argument    *)
(* 'pr' is the printer to be used on subcases.                                *)

let print_hiproof0 pr br h =
  match h with
    Hactive _
       -> print_string "..."
  | Hatomic (id,_)
       -> print_tactic br (gtree_tactic (get_gtree id))
  | Hidentity _
       -> print_string "ALL_TAC"
  | Hlabelled (_,h0)
       -> pr br h0
  | Hsequence (h1, Htensor h2s)
       -> (print_string_if br "(";
           pr false h1;
           print_string " THENL [";
           print_seplist (pr false) "; " h2s;
           print_string "]";
           print_string_if br ")")
  | Hsequence (h1,Hempty)
       -> (pr br h1)
  | Hsequence (h1,h2)
       -> (print_string_if br "(";
           pr false h1;
           print_string " THEN ";
           pr true h2;
           print_string_if br ")")
  | Htensor _
       -> failwith "print_hiproof: Unexpected tensor"
  | Hempty
       -> failwith "print_hiproof: Unexpected empty";;


(* A basic hiproof printer that just uses 'print_hiproof0'.                   *)

let rec print_hiproof1 br h = print_hiproof0 print_hiproof1 br h;;


(* print_hiproof2 *)

let rec print_hiproof2 br h =
  match h with
    Hlabelled (Tactical ("REPEAT", _), Hsequence (h1,h2)) (* if repeated *)
       -> (print_string_if br "(";
           print_string "REPEAT ";
           print_hiproof2 true h1;
           print_string_if br ")")
  | Hlabelled (Tactical ("THEN", _),                     (* if tac2 used *)
               Hsequence (h1, Htensor (h2::h2s)))
       -> (print_string_if br "(";
           print_hiproof2 false h1;
           print_string " THEN ";
           print_hiproof2 true h2;
           print_string_if br ")")
  | Hlabelled (Tactical (("SUBGOAL_THEN",                (* special case *)
                         (Mlterm tm)::[_]) as obj),
               _)
       -> (print_tactic br obj)
  | Hlabelled (Label x, h)
       -> (print_string_if br "(";
           print_string "HILABEL ";
           print_fstring x; print_string " ";
           print_hiproof2 true h;
           print_string_if br ")")
  | _  -> (print_hiproof0 print_hiproof2 br h);;



(* ** PRINTERS ** *)


(* Executed proof *)

(* Prints proof according to how it was executed, i.e. using the original e-  *)
(* steps and according to any user-supplied 'REPEAT' and 'THEN' tacticals,    *)
(* but only those parts that actually execute and not according to any other  *)
(* tacticals.                                                                 *)

let print_hiproof_executed_proof fl h =
  let h' = trivsimp_hiproof h in
  let htrs' = hiproof_block_trace h' in
  do_list (print_hitrace_line_with fl print_hiproof2) htrs';;

let print_gtree_executed_proof fl gtr =
  (print_hiproof_executed_proof fl o gtree_to_hiproof) gtr;;

let print_executed_proof fl = print_gtree_executed_proof fl !the_goal_tree;;


(* Packaged proof *)

(* Prints proof as a monolithic step, spotting opportunities for 'REPEAT' and *)
(* multi-arity 'THEN' tacticals in addition to those already in proof.        *)
(* ! 'REPEAT' not currently catered for.                                      *)

let print_hiproof_packaged_proof h =
  let h' = (trivsimp_hiproof o thenise_hiproof o
            trivsimp_hiproof o leftgroup_hiproof) h in
  print_tactic_line_with print_hiproof2 h';;

let print_gtree_packaged_proof gtr =
  (print_hiproof_packaged_proof o gtree_to_hiproof) gtr;;

let print_packaged_proof () = print_gtree_packaged_proof !the_goal_tree;;


(* THENL proof *)

(* Prints proof as a naive monolithic step, using 'THEN' for single arity,    *)
(* and 'THENL' for multi-arity (even if each subgoal has the same proof).     *)
(* This gives the full structure of each tactic execution.                    *)

let print_hiproof_thenl_proof h =
  let h' = (trivsimp_hiproof o delabel_hiproof) h in
  print_tactic_line_with print_hiproof1 h';;

let print_gtree_thenl_proof gtr =
  (print_hiproof_thenl_proof o gtree_to_hiproof) gtr;;

let print_thenl_proof () = print_gtree_thenl_proof !the_goal_tree;;


(* Flat proof *)

(* This exports a proof as a flat series of e-steps, with no tacticals.       *)

let print_hiproof_flat_proof fl h =
  let h' = (trivsimp_hiproof o rightgroup_hiproof o trivsimp_hiproof o
            delabel_hiproof) h in
  let htrs' = hiproof_block_trace h' in
  do_list (print_hitrace_line_with fl print_hiproof2) htrs';;

let print_gtree_flat_proof fl gtr =
  (print_hiproof_flat_proof fl o gtree_to_hiproof) gtr;;

let print_flat_proof fl = print_gtree_flat_proof fl !the_goal_tree;;
