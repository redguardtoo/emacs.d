(* Library stuff *)

#use "TacticRecording/lib.ml";;
#use "TacticRecording/dltree.mli";;
#use "TacticRecording/dltree.ml";;

(* Datatypes and recording mechanism *)

#use "TacticRecording/mldata.ml";;
#use "TacticRecording/xthm.ml";;
#use "TacticRecording/xtactics.ml";;
#use "TacticRecording/tacticrec.ml";;
#use "TacticRecording/wrappers.ml";;

(* Prooftree support *)

#use "TacticRecording/prooftree.ml";;

(* Hiproofs & refactoring *)

#use "TacticRecording/hiproofs.ml";;

(* Export *)

#use "TacticRecording/printutils.ml";;
#use "TacticRecording/gvexport.ml";;
#use "TacticRecording/mlexport.ml";;

(* Overwriting the existing HOL Light objects *)

#use "TacticRecording/promote.ml";;
