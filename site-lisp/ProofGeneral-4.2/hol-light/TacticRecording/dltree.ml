(* ========================================================================== *)
(* DYNAMIC LOOKUP TREES (HOL Zero)                                            *)
(* - Library support for data storage in dynamic indexed binary trees         *)
(*                                                                            *)
(* By Mark Adams                                                              *)
(* Copyright (c) Proof Technologies Ltd, 2008-2011                            *)
(* ========================================================================== *)


module Dltree : Dltree_sig = struct


(* This module provides library support for operations on dynamic lookup      *)
(* trees - self-balancing binary trees that store information on nodes        *)
(* ordered according to an index under '(<)'-comparison.                      *)

(* This is implemented as Andersson trees (also called AA trees), that stay   *)
(* balanced within a factor of 2 - i.e. the maximum distance from root to     *)
(* leaf is no more than twice the minimum distance.  This has a fairly simple *)
(* implementation and yet is one of the most efficient forms of self-         *)
(* balancing trees.                                                           *)


(* dltree datatype *)

(* The 'dltree' datatype is a binary lookup tree datatype, where an index and *)
(* item are held at each node, and leaves hold no information.  Comparison    *)
(* between indexes is done using the polymorphic '(<)' total order relation.  *)

(* An integer is also held at each node and is used to keep the tree balanced *)
(* as items are inserted/removed.  This integer represents the distance from  *)
(* the node to the left-most leaf descendant of the node.  Thus every left-   *)
(* branch node holds a value 1 less than its parent, and a node with a leaf   *)
(* as its left branch holds value 1.  Every right-branch holds an integer     *)
(* either equal to its parent's or 1 less, and must be strictly less than its *)
(* grandparent's.  Thus the integer at a node also represents an upper bound  *)
(* of half the distance from the node to its rightmost leaf descendant, and   *)
(* thus an upper bound of half the distance from the node to any descendant.  *)

(* The tree is kept balanced by adjusting nodes' integers and left and right  *)
(* branches as the tree is updated.  This is done by the 'skew' and 'split'   *)
(* operations.  The number of nodes that need to be considered in this        *)
(* process is at most O(log n).  Note that reference types are used for a     *)
(* node's branches, to save on unnecessary garbage collection that would      *)
(* otherwise result in rebuilding all ancestor nodes of all adjusted nodes    *)
(* each time a tree is updated.                                               *)

type ('a,'b) dltree0 =
   Node of (int * ('a * 'b) * ('a,'b) dltree * ('a,'b) dltree)
 | Leaf

and ('a,'b) dltree = ('a,'b) dltree0 ref;;


(* dltree_empty : unit -> ('a,'b) dltree                                      *)
(*                                                                            *)
(* Returns a fresh empty dltree.                                              *)

let dltree_empty () = ref Leaf;;


(* dltree_reempty : ('a,'b) dltree -> unit                                    *)
(*                                                                            *)
(* Empties a given dltree.                                                    *)

let dltree_reempty tr = (tr := Leaf);;


(* dltree_elems : ('a,'b) dltree -> ('a * 'b) list                            *)
(*                                                                            *)
(* This converts the information held in a given lookup tree into an index-   *)
(* ordered association list.                                                  *)

let rec dltree_elems0 tr0 xys0 =
  match !tr0 with
    Node (_,xy0,tr1,tr2) -> dltree_elems0 tr1 (xy0::(dltree_elems0 tr2 xys0))
  | Leaf                 -> xys0;;

let dltree_elems tr = dltree_elems0 tr [];;


(* Node destructors *)

let dest_node tr0 =
  match !tr0 with
    Node info -> info
  | Leaf      -> failwith "dest_node: ?";;

let level tr0 =
  match !tr0 with
    Node (l,_,_,_) -> l
  | Leaf           -> 0;;

let left_branch tr0 =
  match !tr0 with
    Node (_,_,tr1,_) -> tr1
  | Leaf             -> failwith "left_branch: No left branch";;

let right_branch tr0 =
  match !tr0 with
    Node (_,_,_,tr2) -> tr2
  | Leaf             -> failwith "right_branch: No right branch";;

let rec leftmost_elem x tr0 =
  match !tr0 with
    Node (_,x0,tr1,_) -> leftmost_elem x0 tr1
  | Leaf              -> x;;

let rec rightmost_elem x tr0 =
  match !tr0 with
    Node (_,x0,_,tr2) -> rightmost_elem x0 tr2
  | Leaf              -> x;;


(* Tests *)

let is_leaf tr0 =
  match !tr0 with
    Leaf -> true
  | _    -> false;;

let is_node tr0 =
  match !tr0 with
    Node _ -> true
  | _      -> false;;


(* skew *)

let skew tr0 =
  if (is_leaf tr0) or (is_leaf (left_branch tr0))
    then ()
  else if (level (left_branch tr0) = level tr0)
    then let (l0,xy0,tr1,tr2) = dest_node tr0 in
         let (l1,xy1,tr11,tr12) = dest_node tr1 in
         (tr0 := Node (l1, xy1, tr11, ref (Node (l0,xy0,tr12,tr2))))
    else ();;


(* split *)

let split tr0 =
  if (is_leaf tr0) or (is_leaf (right_branch tr0))
    then ()
  else if (level (right_branch (right_branch tr0)) = level tr0)
    then let (l0,xy0,tr1,tr2) = dest_node tr0 in
         let (l2,xy2,tr21,tr22) = dest_node tr2 in
         (tr0 := Node (l2 + 1, xy2, ref (Node (l0,xy0,tr1,tr21)), tr22))
    else ();;


(* dltree_insert : 'a * 'b -> ('a,'b) dltree -> unit                          *)
(*                                                                            *)
(* This inserts the supplied single indexed item into a given lookup tree.    *)
(* Fails if the tree already contains an entry for the supplied index.        *)

let rec dltree_insert ((x,_) as xy) tr0 =
  match !tr0 with
    Node (_,(x0,_),tr1,tr2)
       -> ((if (x < x0)
              then (* Put into left branch *)
                   dltree_insert xy tr1
            else if (x0 < x)
              then (* Put into right branch *)
                   dltree_insert xy tr2
              else (* Element already in tree *)
                   failwith "dltree_insert: Already in tree");
           (* Rebalance from the node *)
           skew tr0;
           split tr0)
  | Leaf
       -> (* Put element here *)
          (tr0 := Node (1, xy, ref Leaf, ref Leaf));;


(* dltree_remove : 'a -> ('a,'b) dltree -> unit                               *)
(*                                                                            *)
(* This removes the entry at the supplied index in a given lookup tree.       *)
(* Fails if the tree does not contain an entry for the supplied index.        *)

let decrease_level tr0 =
  let (l0,xy0,tr1,tr2) = dest_node tr0 in
  let n = 1 + min (level tr1) (level tr2) in
  if (n < l0) && (is_node tr2)
    then (tr0 := Node (n,xy0,tr1,tr2);
          if (is_node tr2)
            then let (l2,xy2,tr21,tr22) = dest_node tr2 in
                 if (n < level tr2)
                   then (tr2 := Node (n,xy2,tr21,tr22))
                   else ()
            else ())
    else ();;

let rec dltree_remove x tr0 =
  match !tr0 with
    Node (l0,((x0,_) as xy0),tr1,tr2)
       -> ((if (x < x0)
              then (* Element should be in left branch *)
                   dltree_remove x tr1
            else if (x0 < x)
              then (* Element should be in right branch *)
                   dltree_remove x tr2
              else (* Node holds element to be removed *)
                   if (is_leaf tr1) && (is_leaf tr2)
                     then (tr0 := Leaf)
                   else if (is_leaf tr1)
                     then let (x2,_) as xy2 = leftmost_elem xy0 tr2 in
                          (dltree_remove x2 tr2;
                           tr0 := Node (l0,xy2,tr1,tr2))
                     else let (x1,_) as xy1 = rightmost_elem xy0 tr1 in
                          (dltree_remove x1 tr1;
                           tr0 := Node (l0,xy1,tr1,tr2)));
           (if (is_node tr0)
              then (decrease_level tr0;
                    skew tr0;
                    skew tr2;
                    (if (is_node tr2) then skew (right_branch tr2)
                                      else ());
                    split tr0;
                    split tr2)
              else ()))
  | Leaf
       -> (* Element not in tree *)
          failwith "dltree_remove: Not in tree";;


(* dltree_elem : 'a -> ('a,'b) dltree -> 'a * 'b                              *)
(*                                                                            *)
(* This returns the index and item held at the supplied index in a given      *)
(* lookup tree.  Fails if the tree has no entry for the supplied index.       *)

let rec dltree_elem x0 tr =
  match !tr with
    Node (_, ((x,_) as xy), tr1, tr2)
         -> if (x0 < x)
              then dltree_elem x0 tr1
            else if (x < x0)
              then dltree_elem x0 tr2
              else xy
  | Leaf -> failwith "dltree_elem: Not in tree";;


(* dltree_lookup : 'a -> ('a,'b) dltree -> 'b                                 *)
(*                                                                            *)
(* This returns the item held at the supplied index in a given lookup tree.   *)

let rec dltree_lookup x0 tr =
  let (_,y) = try  dltree_elem x0 tr
              with Failure _ -> failwith "dltree_lookup: Not in tree" in
  y;;


(* dltree_mem : 'a -> ('a,'b) dltree -> bool                                  *)
(*                                                                            *)
(* This returns "true" iff the supplied index occurs in a given lookup tree.  *)

let rec dltree_mem x0 tr =
  match !tr with
    Node (_,(x,_),tr1,tr2)
         -> if (x0 < x)
              then dltree_mem x0 tr1
            else if (x < x0)
              then dltree_mem x0 tr2
              else true
  | Leaf -> false;;


end;;
