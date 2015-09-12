

type mlarg =
   Mlint of int
 | Mlstring of string
 | Mlterm of term
 | Mltype of hol_type
 | Mlthm of mldata
 | Mlpair of mlarg * mlarg
 | Mllist of mlarg list
 | Mlfn of mldata

and mldata = string * mlarg list;;          (* ML object name and args *)


type label =
   Tactical of mldata
 | Label of string;;


(* Atomic tests *)

let is_atomic_mlarg arg =
  match arg with
    Mlthm (_,(_::_)) | Mlpair _ | Mlfn (_, _::_) -> false
  | _ -> true;;

let is_atomic_mldata ((x,args):mldata) = (is_empty args);;


(* active_info *)

let active_info = ("...",[]);;
