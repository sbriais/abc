module type OrderedType =
  sig
    type t
    val compare : t -> t -> int
  end

module type S =
  sig
    type elt
    type t
    val empty : t
    val add : elt * elt -> t -> t
    val canonical_substitution : t -> elt -> elt
    val equivalent : elt -> elt -> t -> bool
    val implies : t -> t -> bool
    val union : t -> t -> t
    val for_all : (elt -> bool) -> t -> bool
    val map : (elt -> elt) -> t -> t
    val elements : t -> elt list list
    val compare : t -> t -> int
  end

module Make (Ord:OrderedType) : S with type elt = Ord.t
