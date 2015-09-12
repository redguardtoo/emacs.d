(* ========================================================================== *)
(* HIPROOFS (HOL LIGHT)                                                       *)
(* - Hiproofs and refactoring operations                                      *)
(*                                                                            *)
(* By Mark Adams                                                              *)
(* Copyright (c) Univeristy of Edinburgh, 2012                                *)
(* ========================================================================== *)


(* This file defines a hiproof [1] datatype and various operations on it.     *)
(* The datatype closely resembles that proposed in [2], with the notable      *)
(* difference that atomic steps carry their arity.                            *)

(* [1] "Hiproofs: A Hierarchical Notion of Proof Tree", Denney, Power &       *)
(*    Tourlas, 2006.                                                          *)
(* [2] "A Tactic Language for Hiproofs", Aspinall, Denney & Luth, 2008.       *)



(* ** DATATYPE ** *)


(* Hiproof datatype *)

(* Note that atomic tactics are labelled with their arity, corresponding to   *)
(* how many subgoals they result in.  An arity of -1 indicates unknown, and 0 *)
(* indicates a tactic that completes its goal.                                *)

type hiproof =
    Hactive of goalid                   (* Active subgoal *)
  | Hatomic of (goalid * int)           (* Atomic tactic + arity *)
  | Hidentity of goalid                 (* Null, for wiring *)
  | Hlabelled of (label * hiproof)      (* Box *)
  | Hsequence of (hiproof * hiproof)    (* Serial application *)
  | Htensor of hiproof list             (* Parallel application *)
  | Hempty;;                            (* Completed goal *)


(* Constructors and destructors *)

let hsequence (h1,h2) = Hsequence (h1,h2);;

let dest_hsequence h =
  match h with
    Hsequence hh -> hh
  | _   -> failwith "Not a sequence hiproof";;

let is_hsequence h = can dest_hsequence h;;

let is_hidentity h = match h with Hidentity _ -> true | _ -> false;;

let hiproof_id h =
  match h with
    Hactive id | Hatomic (id,_) | Hidentity id -> id
  | _  -> failwith "hiproof_id: Not a unit hiproof";;


(* Arity *)

let rec hiproof_arity h =
  match h with
    Hactive _         -> 1
  | Hatomic (_,n)     -> n
  | Hidentity _       -> 1
  | Hlabelled (_,h0)  -> hiproof_arity h0
  | Hsequence (h1,h2) -> hiproof_arity h2
  | Htensor hs        -> sum (map hiproof_arity hs)
  | Hempty            -> 0;;


(* Hitrace *)

type hitrace =
   Hicomment of int list
 | Hiproof of hiproof;;



(* ** TRANSLATION OF GOAL TREE TO HIPROOF ** *)


let rec gtree_to_hiproof gtr =
  let id = gtree_id gtr in
  let (_,gtrm) = gtr in
  match !gtrm with
    Gactive
       -> Hactive id
  | Gexit _
       -> Hidentity id
  | Gexecuted (gstp,gtrs)
       -> let h1 =
             match gstp with
               Gatom _ | Gbox (_,_,true)
                  -> Hatomic (id, length gtrs)
             | Gbox (l,gtr,false)
                  -> Hlabelled (l, gtree_to_hiproof gtr) in
          let h2 = Htensor (map gtree_to_hiproof gtrs) in
          Hsequence (h1,h2);;



(* ** REFACTORING OPERATIONS ** *)


(* Generic refactoring operation *)

(* Applies a refactoring function 'foo' at every level of hiproof 'h', from   *)
(* bottom up.  If the 'r' flag is set then refactoring is repeated bottom up  *)
(* whenever 'foo' makes a change.  Note that if 'foo' makes no change then it *)
(* should just return its input hiproof (rather than raise an exception).     *)

let rec refactor_hiproof r foo h =
  let h' =
     match h with
       Hlabelled (l,h0)
          -> let h0' = refactor_hiproof r foo h0 in
             Hlabelled (l,h0')
     | Hsequence (h1,h2)
          -> let h1' = refactor_hiproof r foo h1 in
             let h2' = refactor_hiproof r foo h2 in
             Hsequence (h1',h2')
     | Htensor hs
          -> let hs' = map (refactor_hiproof r foo) hs in 
             Htensor hs'
     | _  -> h in
  let h'' = if (h' = h) then h else h' in
  let h''' = foo h'' in
  if r & not (h''' = h'')
    then refactor_hiproof r foo h'''
    else h''';;


(* Trivial simplification *)

(* Removes basic algebraic identities/zeros.                                  *)

let collapse_tensor h hs =
  match h with
    Hempty      -> hs
  | Htensor hs0 -> hs0 @ hs
  | _           -> h :: hs;;

let trivsimp_hiproof h =
  let trivsimp h =
     match h with
       Hatomic (id,_) when (gtree_tactic (get_gtree id) = ("ALL_TAC",[]))
                                   -> Hidentity id
     | Hsequence (h1, Hempty)      -> h1
     | Hsequence (h1, Hidentity _) -> h1
     | Hsequence (h1, Htensor hs2) -> if (forall is_hidentity hs2)
                                        then h1
                                        else h
     | Hsequence (Hidentity _, h2) -> h2
     | Hsequence (Htensor hs1, h2) -> if (forall is_hidentity hs1)
                                        then h2
                                        else h
     | Htensor []                  -> Hempty
     | Htensor [h0]                -> h0
     | Htensor hs0                 -> Htensor (foldr collapse_tensor hs0 [])
     | _  -> h in
  refactor_hiproof true trivsimp h;;


(* Matching up two tensored lists to create single tensored list *)

let rec matchup_hiproofs0 hs1 hs2 =
  match hs1 with
    [] -> []
  | h1::hs01
       -> let n1 = hiproof_arity h1 in
          let (hs2a,hs2b) = try chop_list n1 hs2
                with Failure _ ->
                     if (n1 = -1)
                       then failwith "matchup_hiproofs: unknown arity"
                       else failwith "matchup_hiproofs: Internal error - \
                                                      inconsistent arities" in
          (h1,hs2a) :: (matchup_hiproofs0 hs01 hs2b);;

let matchup_hiproofs hs1 hs2 =
  let hhs = matchup_hiproofs0 hs1 hs2 in
  map (fun (h1,hs2) -> Hsequence (h1, Htensor hs2)) hhs;;


(* Separating out tensored list into head tensor and tail tensor  *)

let separate_hiproofs0 h (hs01,hs02) =
  match h with
    Hsequence (h1,h2)
       -> (h1::hs01, h2::hs02)
  | _  -> let n = hiproof_arity h in
          let h2 = Htensor (copy n (Hidentity (-1))) in
          (h::hs01, h2::hs02);;

let separate_hiproofs hs = foldr separate_hiproofs0 hs ([],[]);;


(* Delabelling *)

(* Strips out any boxes from the proof.  Note that some boxes, such as        *)
(* 'SUBGOAL_THEN', cannot be stripped out without spoiling the proof, and so  *)
(* are left alone.                                                            *)

let delabel_hiproof h =
  let delabel h =
     match h with
       Hlabelled (Tactical ("SUBGOAL_THEN",_), h0)
          -> h
     | Hlabelled (_,h0)
          -> h0
     | _  -> h in
  refactor_hiproof true delabel h;;

let dethen_hiproof h =
  let dethen h =
     match h with
       Hlabelled (Tactical (("THEN" | "THENL"),_), h0)
          -> h0
     | _  -> h in
  refactor_hiproof true dethen h;;


(* Right-grouping *)

(* Expands the proof into a right-associative sequence, with tensor           *)
(* compounding on the right.  Leaves all boxes unchanged.                     *)

let rightgroup_hiproof h =
  let rightgroup h =
     match h with
       Hsequence (Hsequence (h1, Htensor hs2), Htensor hs3)
          -> Hsequence (h1, Htensor (matchup_hiproofs hs2 hs3))
     | Hsequence (Hsequence (h1, Htensor hs2), h3)
          -> Hsequence (h1, Htensor (matchup_hiproofs hs2 [h3]))
     | Hsequence (Hsequence (h1,h2), h3)
          -> Hsequence (h1, Hsequence (h2,h3))
     | _  -> h in
  refactor_hiproof true rightgroup h;;


(* Left-grouping *)

(* Expands the proof into a left-associative sequence.                        *)

let leftgroup_hiproof h =
  let leftgroup h =
     match h with
       Hsequence (h1, Hsequence (h2, h3))
          -> Hsequence (Hsequence (h1,h2), h3)
     | _  -> h in
  refactor_hiproof true leftgroup h;;


(* THEN insertion *)

(* Looks for opportunities to use 'THEN' tacticals.  Note that assumes a      *)
(* normal form where trivsimp has taken place.                                *)

let rec head_hiproof_equiv h1 h2 =
  match (h1,h2) with
    (Hatomic (id1,_), Hatomic (id2,_))
       -> (gtree_tactic o get_gtree) id1 = (gtree_tactic o get_gtree) id2
  | (Hidentity _, Hidentity _)
       -> true
  | (Hsequence (h1a,h1b), h2)
       -> head_hiproof_equiv h1a h2
  | (h1, Hsequence (h2a,h2b))
       -> head_hiproof_equiv h1 h2a
  | (Hempty, Hempty)
       -> true
  | _  -> false;;

let thenise_hiproof h =
  let rec thenise h =
     match h with
       Hsequence (h1, Htensor (h2::h2s))
          -> if not (is_hidentity h2) & (forall (head_hiproof_equiv h2) h2s) 
               then let (hs2a,hs2b) = separate_hiproofs (h2::h2s) in
                    let h' = Hsequence
                               (Hlabelled (Tactical ("THEN",[]),
                                           Hsequence (h1, Htensor hs2a)),
                                Htensor hs2b) in
                    thenise h'
               else h
     | _  -> h in
  refactor_hiproof false thenise h;;



(* ** HIPROOF GRAPH ** *)


(* Graph element datatype *)

type graph_elem =
    Box of (label * graph_elem list)
  | Line of (goalid * goalid)
  | Single of goalid
  | Name of (goalid * string);;

let is_box ge =
  match ge with Box _ -> true | _ -> false;;

let mk_line id1 id2 = Line (id1,id2);;

let rec graph_elem_nodes ge =
  match ge with
    Box (_,ges)    -> graph_nodes ges
  | Line (id1,id2) -> [id1;id2]
  | Single id      -> [id]
  | Name (id,x)    -> [id]

and graph_nodes ges =
  foldr (fun ge ids -> union (graph_elem_nodes ge) ids) ges [];;


(* Utils *)

let rec hiproof_ins h =
  match h with
    Hactive id        -> [id]
  | Hatomic (id,n)    -> [id]
  | Hidentity id      -> [-1]
  | Hlabelled (l,h0)  -> hiproof_ins h0
  | Hsequence (h1,h2) -> hiproof_ins h1
  | Htensor hs        -> flat (map hiproof_ins hs)
  | Hempty            -> [];;

let rec hiproof_outs (h:hiproof) : goalid list =
  match h with
    Hactive id        -> [id]
  | Hatomic (id,n)    -> copy n id
  | Hidentity id      -> [id]
  | Hlabelled (l,h0)  -> hiproof_outs h0
  | Hsequence (h1, Htensor hs2)
       -> let nhs2 = enumerate hs2 in
          let ids1 = hiproof_outs h1 in
          let foo (n2,h2) =
             if (is_hidentity h2) then [el (n2-1) ids1]
                                  else hiproof_outs h2 in
          flat (map foo nhs2)
  | Hsequence (h1,h2) -> hiproof_outs h2
  | Htensor hs        -> flat (map hiproof_outs hs)
  | Hempty            -> [];;


(* Graph production *)

let rec hiproof_graph0 h =
  match h with
    Hactive _      -> []
  | Hatomic _      -> []
  | Hidentity _    -> []
  | Hlabelled (l,Hatomic (id,_))
       -> [Box (l, [Single id])]
  | Hlabelled (l,h0)
       -> [Box (l, hiproof_graph0 h0)]
  | Hsequence (h1,h2)
       -> let idids = zip (hiproof_outs h1) (hiproof_ins h2) in
          let idids' = filter (fun (_,id2) -> (id2 > 0)) idids in
          (hiproof_graph0 h1) @
          (map (fun idid -> Line idid) idids') @
          (hiproof_graph0 h2)
  | Htensor hs     -> flat (map hiproof_graph0 hs)
  | Hempty         -> [];;

let hiproof_graph h =
  let ges = hiproof_graph0 h in
  let ids = graph_nodes ges in
  let tacname_of_id id = (fst o gtree_tactic1 o get_gtree) id in
  let ges' = map (fun id -> Name (id, tacname_of_id id)) ids in
  ges' @ ges;;



(* ** OTHER OPERATIONS ** *)


(* Tactic trace *)

(* Gives a linear trace of the basic tactics used in the proof, ignoring how  *)
(* they were combined by tacticals.                                           *)

let rec hiproof_tactic_trace0 h =
  match h with
    Hactive _
       -> [active_info]
  | Hatomic (id, _)
       -> [gtree_tactic (get_gtree id)]
  | Hidentity _
       -> []
  | Hlabelled (_,h0)
       -> hiproof_tactic_trace0 h0
  | Hsequence (h1,h2)
       -> (hiproof_tactic_trace0 h1) @ (hiproof_tactic_trace0 h2)
  | Htensor hs
       -> flat (map hiproof_tactic_trace0 hs)
  | Hempty
       -> [];;

let hiproof_tactic_trace h = (hiproof_tactic_trace0 o delabel_hiproof) h;;


(* Block trace *)

(* Gives a linear trace of the hiproofs used in the proof, stopping at boxes. *)

let rec hiproof_block_trace0 ns0 h =
  match h with
  | Hsequence (h1,h2)
       -> (hiproof_block_trace0 ns0 h1) @ (hiproof_block_trace0 ns0 h2)
  | Htensor hs
       -> let nss = map (fun n -> ns0 @ [n]) (1 -- length hs) in
          flat (map (fun (ns,h) -> (Hicomment ns) :: hiproof_block_trace0 ns h)
                    (zip nss hs))
  | _  -> [Hiproof h];;

let hiproof_block_trace h = hiproof_block_trace0 [] h;;
