module type OrderedType =
sig
  type t
  val compare : t -> t -> int
end

module type S =
sig
  type elt
  type elt_cond
  type t
  val empty : t
  val is_empty : t -> bool
  val add : elt * elt -> t -> t
  val subset : t -> t -> bool
  val union : t -> t -> t
  val respects : elt_cond -> t -> bool
  val prune : elt list -> t -> t
  val generate : elt list -> elt list -> t
  val pwd : elt list -> t
  val map : (elt -> elt) -> t -> t
  val elements : t -> (elt * elt) list
  val compare : t -> t -> int
end

module Make (Ord:OrderedType) (EltCond:Conditions.S with type elt = Ord.t) =
struct
  type elt = Ord.t
  type elt_cond = EltCond.t

  module Elt2Set = Set.Make(struct 
			      type t = Ord.t * Ord.t
			      let compare (x0,y0) (x1,y1) =
				match Ord.compare x0 x1 with
				    0 -> Ord.compare y0 y1
				  | t -> t
			    end)
  type t = Elt2Set.t
	     
  let empty = Elt2Set.empty

  let is_empty = Elt2Set.is_empty

  let norm (n,m) = 
    match Ord.compare n m with
	t when t <= 0 -> (n,m)
      | _ -> (m,n) 

  let add (n,m) d =
    if (Ord.compare n m) = 0 then failwith "Distinctions.add"
    else Elt2Set.add (norm (n,m)) d

  let subset = Elt2Set.subset

  let union = Elt2Set.union

  let respects c d =
    Elt2Set.for_all (function (n,m) -> not (EltCond.equivalent n m c)) d

  let mem x l =
    List.exists (function y -> (Ord.compare x y) = 0) l

  let prune l d =
    Elt2Set.filter (function (n,m) -> (mem n l) && (mem m l)) d

  let generate l l' =
    List.fold_left (fun d x -> List.fold_left (fun d y -> add (x,y) d) d l') empty l

  let pwd l =
    List.fold_left (fun d x -> List.fold_left (fun d y -> if (Ord.compare x y) = 0 then d else add (x,y) d) d l) empty l

  let map f d =
    Elt2Set.fold (fun (n,m) d -> add (f n,f m) d) d empty

  let elements d =
    Elt2Set.elements d

  let compare = Elt2Set.compare
end
