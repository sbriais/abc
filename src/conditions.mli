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
