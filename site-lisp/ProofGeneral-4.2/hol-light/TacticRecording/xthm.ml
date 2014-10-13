


(* ** DATATYPE ** *)


(* The 'xthm' datatype *)

(* This couples a theorem with an 'mldata' representation of its proof.  For  *)
(* named ML objects, this 'mldata' will simply be the ML name of the theorem. *)
(* For rule applications, it will capture the rule and its arguments.         *)

type xthm = thm * mldata;;

type xconv = term -> xthm;;


(* Constructors and destructors *)

let mk_xthm (xth:thm*mldata) : xthm = xth;;

let mk_xthm0 x th = mk_xthm (th, (x,[]));;

let dest_xthm ((th,prf):xthm) : thm * mldata = (th,prf);;

let xthm_thm ((th,_):xthm) = th;;

let xthm_proof ((_,prf):xthm) = prf;;

let name_xthm x ((th,_):xthm) : xthm = (th, (x,[]));;



(* ** INSTALL PRINTERS ** *)


let print_xthm ((th,_):xthm) = print_thm th;;

#install_printer print_xthm;;

