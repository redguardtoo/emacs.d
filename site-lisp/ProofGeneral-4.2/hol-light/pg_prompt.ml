(* ========================================================================= *)
(* HOL Light tweaks for Proof General.				             *)
(*                                                                           *)
(* Mark Adams, David Aspinall.						     *)
(* LFCS, School of Informatics, University of Edinburgh			     *)
(*                                                                           *)
(* (c) Copyright University of Edinburgh and authors, 2012.                  *)
(*									     *)
(* This file adjust the OCaml prompt to help Proof General synchronization.  *)
(* It is loaded before HOL Light.					     *)
(* ========================================================================= *)


(* ------------------------------------------------------------------------- *)
(* Proof General mode, providing extra annotations in output	             *)
(* ------------------------------------------------------------------------- *)

let pg_mode = ref (true : bool);;

let pg_mode_on () = (pg_mode := true);;
let pg_mode_off () = (pg_mode := false);;

let pg_prompt_info = ref (fun () -> "");;


(* ------------------------------------------------------------------------- *)
(* Adjust the OCaml prompt to carry information for Proof General            *)
(* ------------------------------------------------------------------------- *)

let original_prompt_fn = !Toploop.read_interactive_input in
(Toploop.read_interactive_input :=
   fun prompt buffer len ->
      let prompt' =
         if (!pg_mode)
           then "<prompt>" ^
		(!pg_prompt_info()) ^
                "</prompt>"
           else prompt in
      original_prompt_fn prompt' buffer len);;


(* ------------------------------------------------------------------------- *)
(* Adjust error printing to markup error messages			     *)
(* ------------------------------------------------------------------------- *)

(* Doesn't really work, as many errors are from OCaml top level and
   not printed in this way.

let print_exn e =
    match e with
      Failure x -> Format.print_string 
		     (if (!pg_mode) then 
		         "<error>" ^ x ^ "</error>"
		      else x)
    | _  -> Format.print_string (Printexc.to_string e);;

#install_printer print_exn;;

*) 
