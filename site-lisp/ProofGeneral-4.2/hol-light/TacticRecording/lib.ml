
let rec copy n x =
  if (n > 0) then x::(copy (n-1) x)
             else [];;


let rec enumerate0 n xs =
  match xs with
    []     -> []
  | x::xs0 -> (n,x)::enumerate0 (n+1) xs0;;
let enumerate xs = enumerate0 1 xs;;


(* foldr : ('a -> 'b -> 'b) -> 'a list -> 'b -> 'b                            *)

let rec foldr f xs a =
  match xs with
    x1::xs2 -> f x1 (foldr f xs2 a)
  | []      -> a;;


(* foldr1 : ('a -> 'a -> 'a) -> 'a list -> 'a                                 *)

let rec foldr1 f xs =
  match xs with
    x::[]   -> x
  | x1::xs2 -> f x1 (foldr1 f xs2)
  | []      -> failwith "foldr1: Empty list";;


(* foldl : ('b -> 'a -> 'b) -> 'b -> 'a list -> 'b                            *)

let rec foldl f a xs =
  match xs with
    x1::xs2 -> foldl f (f a x1) xs2
  | []      -> a;;


(* is_empty *)

let is_empty xs =
  match xs with
    [] -> true
  | _  -> false;;


(* front *)

let rec front xs =
  match xs with
    _::[]   -> []
  | x0::xs0 -> x0::(front xs0)
  | []      -> failwith "front: Empty list";;


(* string_option *)

let string_option x0 x_ =
  match x_ with
    Some x -> x
  | None   -> x0;;


(* print_option *)

let print_option x0 x_ =
  match x_ with
    Some x -> print_string x
  | None   -> print_string x0;;


(* seplists *)

let print_seplist p sep xs =
  if (xs = [])
    then ()
    else (p (hd xs);
          do_list (fun x -> print_string sep; p x) (tl xs));;

let print_string_seplist sep xs =
  print_seplist print_string sep xs;;


(* sum *)

let sum ns = foldl (+) 0 ns;;


(* snd_map *)

let snd_map f xys = map (fun (x,y) -> (x, f y)) xys;;
