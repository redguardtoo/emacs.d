(* ========================================================================== *)
(* GRAPHVIZ EXPORT (HOL LIGHT)                                                *)
(* - Exporting recorded tactics into a Dot file for GraphViz                  *)
(*                                                                            *)
(* By Mark Adams                                                              *)
(* Copyright (c) Univeristy of Edinburgh, 2012                                *)
(* ========================================================================== *)


let cluster_count = ref 0;;

let rec print_gv_graphelem d ge =
  match ge with
    Box (l,ges)
       -> let () = (cluster_count := !cluster_count + 1) in
          (print_indent d; print_string "subgraph cluster";
             print_int !cluster_count; print_string " "; print_string "{\n";
           print_indent (d+2); print_string "label = "; print_label l;
             print_string ";\n";
           do_list (print_gv_graphelem (d+2)) ges;
           print_indent d; print_string "}\n")
  | Line (id1,id2)
       -> (print_indent d; print_goalid id1; print_string " -> ";
             print_goalid id2; print_string ";\n")
  | Single id
       -> (print_indent d; print_goalid id; print_string ";\n")
  | Name (id,x)
       -> (print_indent d; print_goalid id;
             print_string " [label = "; print_fstring x; print_string "];\n");;

let print_gv_graph ges =
  let () = (cluster_count := 0) in
  (print_string "digraph G {\n";
   do_list (print_gv_graphelem 2) ges;
   print_string "}\n");;

let print_hiproof_gv_graph h =
  let h' = (trivsimp_hiproof o rightgroup_hiproof o
            trivsimp_hiproof o dethen_hiproof) h in
  let ges = hiproof_graph h' in
  print_gv_graph ges;;

let print_gtree_gv_proof gtr =
  let h = gtree_to_hiproof gtr in
  print_hiproof_gv_graph h;;

let print_gv_proof () = print_gtree_gv_proof !the_goal_tree;;
