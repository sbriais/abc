(* les noms sont isomorphes aux entiers *)

type t = int

type substitution = t -> t

let zero = 0

let succ x = x+1

let pred = function
    0 -> failwith "Name.pred"
  | n -> (n-1)

let compare x y = compare x y

let is_zero = function
    0 -> true
  | _ -> false

let plus n x =
  let y = x+n in
    if y >= 0 then y
    else failwith "Name.plus"

(* lvl est le nombre de lieurs déjà rencontrés *)
let is_free lvl n = 
  if n >= lvl then true
  else false

let freename lvl n =
  if n >= lvl then n-lvl
  else failwith "Name.get_name"

let substitute sigma lvl x =
  if x >= lvl then (sigma (x-lvl))+lvl
  else x

let to_string lvl n =
(*
  (string_of_int lvl)^" : "^(string_of_int n)
*)
  if n >= lvl then "%"^(string_of_int (n-lvl))
  else "x"^(string_of_int (lvl-n-1))

(* apply_subst lvl l sigma build the substitution such that if n is bound (ie n < lvl) *)
(* then, it is mapped to the corresponding name in the list l *)
(* otherwise n is mapped to sigma(n-lvl) (we have removed lvl binders) *)
(* note that length(l) = lvl *)
let apply_substitution lvl l sigma n =
  if n < lvl then List.nth l (lvl-n-1)
  else sigma (n-lvl)

let of_int n =
  if n < 0 then failwith "Name.of_int"
  else n

let freshnames n l =
(*
  let m = List.fold_left max 0 l in
  let rec n_from from = function
      0 -> []
    | n -> from::(n_from (from+1) (n-1))
  in
    n_from (m+1) n
*)
  let rec n_from from = function
      0 -> []
    | n -> 
	if List.mem from l then n_from (from+1) n
	else from::(n_from (from+1) (n-1))
  in
    n_from 0 n
