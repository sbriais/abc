(* 
#  This program is free software; you can redistribute it and/or modify
#  it under the terms of the GNU General Public License as published by
#  the Free Software Foundation; either version 2 of the License, or
#  (at your option) any later version.
#
#  This program is distributed in the hope that it will be useful,
#  but WITHOUT ANY WARRANTY; without even the implied warranty of
#  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
#  GNU General Public License for more details.
#
#  You should have received a copy of the GNU General Public License
#  along with this program; if not, write to the Free Software
#  Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307,
#  USA. 
*)
type 'a multiset

module type OrderedType =
sig
  type t
  val compare: (t multiset -> t multiset -> int) -> t -> t -> int
end

module type S =
sig
  type elt
  type t = elt multiset
  val empty: t
  val is_empty: t -> bool
  val mem: elt -> t -> bool
  val add: elt -> int -> t -> t
  val singleton: elt -> t
  val remove: elt -> int -> t -> t
  val union: t -> t -> t
  val inter: t -> t -> t
  val diff: t -> t -> t
  val duplicate : int -> t -> t
  val compare: t -> t -> int
  val equal: t -> t -> bool
  val subset: t -> t -> bool
  val iter: (elt -> int -> unit) -> t -> unit
  val fold: (elt -> int -> 'a -> 'a) -> t -> 'a -> 'a
  val multifold : (elt -> 'a -> 'a) -> t -> 'a -> 'a
  val map: (elt -> elt) -> t -> t
  val for_all: (elt -> int -> bool) -> t -> bool
  val exists: (elt -> int -> bool) -> t -> bool
  val filter: (elt -> int -> bool) -> t -> t
  val partition: (elt -> int -> bool) -> t -> t * t
  val cardinal: t -> int
  val elements: t -> elt list
  val elements_packed: t -> (elt * int) list
  val min_elt: t -> elt
  val max_elt: t -> elt
  val choose: t -> elt
  val of_list: (elt * int) list -> t
end

module Make(Ord: OrderedType) : S with type elt = Ord.t and type t = Ord.t multiset
