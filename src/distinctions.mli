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

module Make (Ord:OrderedType) (EltCond:Conditions.S with type elt = Ord.t) : S with type elt = Ord.t and type elt_cond = EltCond.t
