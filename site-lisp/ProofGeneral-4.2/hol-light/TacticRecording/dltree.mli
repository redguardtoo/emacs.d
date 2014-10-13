(* ========================================================================== *)
(* DYNAMIC LOOKUP TREES (HOL Zero)                                            *)
(* - Library support for data storage in dynamic indexed binary trees         *)
(*                                                                            *)
(* By Mark Adams                                                              *)
(* Copyright (c) Proof Technologies Ltd, 2008-2011                            *)
(* ========================================================================== *)


module type Dltree_sig = sig

  type ('a,'b) dltree
  val dltree_empty : unit -> ('a,'b) dltree
  val dltree_reempty : ('a,'b) dltree -> unit
  val dltree_mem : 'a -> ('a,'b) dltree -> bool
  val dltree_lookup : 'a -> ('a,'b) dltree -> 'b
  val dltree_elem : 'a -> ('a,'b) dltree -> 'a * 'b
  val dltree_elems : ('a,'b) dltree -> ('a * 'b) list
  val dltree_insert : ('a * 'b) -> ('a,'b) dltree -> unit
  val dltree_remove : 'a -> ('a,'b) dltree -> unit

end;;
