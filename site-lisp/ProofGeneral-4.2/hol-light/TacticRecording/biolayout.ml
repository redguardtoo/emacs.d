(* ========================================================================== *)
(* BIOLAYOUT EXPORT (HOL LIGHT)                                               *)
(* - Support for BioLayout graph display of recorded tactics                  *)
(*                                                                            *)
(* By Mark Adams                                                              *)
(* Copyright (c) Univeristy of Edinburgh, 2012                                *)
(* ========================================================================== *)


(* biolayout_nodename *)

let biolayout_nodename n =
  "Node" ^ string_of_int n;;


(* biolayout_export *)

let biolayout_export path name =
  let nns = gtree_graph () in
  let suffix = ".layout" in
  let fullname = Filename.concat path (name ^ suffix) in
  let ch = open_out fullname in
  let export_line ch (n1,n2) =
     (output_string ch (biolayout_nodename n1);
      output_string ch "\t";
      output_string ch (biolayout_nodename n2);
      output_string ch "\n") in
  (print_string ("Exporting to file \"" ^ fullname ^ "\"\n");
   do_list (export_line ch) nns;
   close_out ch);;
