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

module Make(Ord:OrderedType) =
struct
  type elt = Ord.t
  module EltSet = Set.Make(Ord)
  module EltSetSet = Set.Make(EltSet)
  type t = EltSetSet.t
	     
  let empty = EltSetSet.empty
		
  let add (n,m) cs = 
    if Ord.compare n m = 0 then cs
    else
      let (cs,s) = EltSetSet.fold (fun c (ds,s) ->
				     (match s with
					  None ->
					    if EltSet.mem n c then (ds,Some(EltSet.add m c))
					    else
					      if EltSet.mem m c then (ds,Some(EltSet.add n c))
					      else (EltSetSet.add c ds,None)
					| Some(d) ->
					    if (EltSet.mem n c) || (EltSet.mem m c) then (ds,Some(EltSet.union c d))
					    else (EltSetSet.add c ds,Some(d)))) cs (empty,None) in
	(match s with
	     Some(d) -> EltSetSet.add d cs
	   | None -> EltSetSet.add (EltSet.add n (EltSet.singleton m)) cs)

  exception Found of elt

  let canonical_substitution cs n =
    (try
       ignore (EltSetSet.exists (function c -> if EltSet.mem n c then raise (Found(EltSet.min_elt c)) else false) cs);
       n
     with Found(r) -> r)

  exception Equivalent

  let equivalent n m cs = 
    (try
       EltSetSet.exists (function c -> if (EltSet.mem n c) && (EltSet.mem m c) then raise Equivalent else false) cs
     with Equivalent -> true)

  let implies cs ds =
    EltSetSet.for_all (function d -> EltSetSet.exists (function c -> EltSet.subset d c) cs) ds
      
  let union css dss =
    EltSetSet.fold (fun cs ess -> 
		      let min_cs = EltSet.min_elt cs in
			EltSet.fold (fun c ess -> add (min_cs,c) ess) cs ess) dss css

  let for_all p css =
    EltSetSet.for_all (EltSet.for_all p) css

  let map f css =
    EltSetSet.fold (fun cs ess -> 
		      let fmin_cs = f (EltSet.min_elt cs) in
			EltSet.fold (fun c ess -> add (fmin_cs,f c) ess) cs ess) css empty
      
  let elements css = 
    List.map EltSet.elements (EltSetSet.elements css)

  let compare = EltSetSet.compare
end
