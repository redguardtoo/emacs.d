(* ========================================================================== *)
(* PRINTER UTILITIES (HOL LIGHT)                                              *)
(* - Various basic utilities used in writing the exporters                    *)
(*                                                                            *)
(* By Mark Adams                                                              *)
(* Copyright (c) Univeristy of Edinburgh, 2012                                *)
(* ========================================================================== *)


(* Basics *)

let print_string_if b x = if b then print_string x;;

let print_fstring x = print_string ("\"" ^ String.escaped x ^ "\"");;

let print_fterm tm = print_string ("`" ^ string_of_term tm ^ "`");;

let print_ftype ty = print_string ("`" ^ string_of_type ty ^ "`");;

let print_goalid id = print_int id;;

let print_indent d = print_string (String.make d ' ');;


(* Printer for 'mldata' *)

let rec print_mlarg br arg =
  match arg with
    Mlint n       -> print_int n
  | Mlstring x    -> print_fstring x
  | Mlterm tm     -> print_fterm tm
  | Mltype ty     -> print_ftype ty
  | Mlthm prf     -> print_mldata br prf
  | Mlpair (arg1,arg2)
       -> let sep =
             if (forall is_atomic_mlarg [arg1;arg2]) then "," else ", " in
          (print_string_if br "(";
           print_mlarg false arg1;
           print_string sep;
           print_mlarg false arg2;
           print_string_if br ")")
  | Mllist args 
       -> let sep = if (forall is_atomic_mlarg args) then ";" else "; " in
          (print_string "[";
           print_seplist (print_mlarg false) sep args;
           print_string "]")
  | Mlfn f
       -> (print_mldata br f)

and print_mldata br ((x,args):mldata) =
  (print_string_if (br & not (is_empty args)) "(";
   print_string x;
   do_list (fun arg -> print_string " "; print_mlarg true arg) args;
   print_string_if (br & not (is_empty args)) ")");;


(* Printer for labels *)

let print_label l =
  match l with
    Tactical (x,_) | Label x  -> print_fstring x;;
