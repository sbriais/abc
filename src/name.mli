type t

type substitution = t -> t

val zero : t
val succ : t -> t
val pred : t -> t
val compare : t -> t -> int
val is_zero : t -> bool
val plus : int -> t -> t
val is_free : int -> t -> bool
val freename : int -> t -> t
val substitute : substitution -> int -> substitution
val to_string : int -> t -> string
val apply_substitution : int -> t list -> substitution -> substitution
val of_int : int -> t
val freshnames : int -> t list -> t list
