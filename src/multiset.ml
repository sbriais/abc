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
type 'a multiset = ('a * int) list

(* astuce pour contourner l'interdiction des modules mutuellement récursifs *)
(* permet d'avoir un type de données construit avec des multiset *)
(* le prix à payer est que l'abstraction sur l'implémentation n'est pas totale *)
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

(* les multiset sont représentés par une liste de couples triées en ordre décroissant *)
(* la première composante est l'élément, la seconde est le nombre de répétitions *)
(* comme montré dans le All That (Bader, Nipkow), l'ordre multiset est facile à implémenter *)
(* avec une telle représentation *)
(* les autres opérations ne posent pas de problèmes majeurs *)
module Make(Ord: OrderedType) =
struct
  type elt = Ord.t
  type t = elt multiset

  let rec compare (m1:t) (m2:t) = 
    let rec aux = function
	[],[] -> 0
      | [],_ -> -1
      | _,[] -> 1
      | ((x,n)::ms,(y,p)::ns) ->
	  (match Ord.compare compare x y with
	       0 -> 
		 (if n = p then (aux (ms,ns))
		  else
		    if n > p then 1 
		    else -1)
	     | t -> t)
    in
      aux (m1,m2)

  let empty = ([]:t)

  let is_empty = function
      ([]:t) -> true
    | _ -> false

  let rec mem (x:elt) = function
      ([]:t) -> false
    | (y,n)::tail -> 
	(match Ord.compare compare x y with
	     0 -> true
	   | t when t < 0 -> mem x tail
	   | _ -> false)

  let rec add (x:elt) n = function
      ([]:t) -> ([x,n]:t)
    | (y,p)::tail ->
	(match Ord.compare compare x y with
	     0 -> (y,p+n)::tail
	   | t when t < 0 -> (y,p)::(add x n tail)
	   | _ -> (x,n)::(y,p)::tail)

  let singleton x = add x 1 empty

  let rec remove (x:elt) n = function
      ([]:t) -> ([]:t)
    | (y,p)::tail ->
	(match Ord.compare compare x y with
	     0 -> if p <= n then tail else (y,p-n)::tail
	   | t when t < 0 -> (y,p)::(remove x n tail)
	   | _ -> (y,p)::tail)

  let union (m1:t) (m2:t) =
    let rec aux = function
	([],n) -> n
      | (m,[]) -> m
      | ((x,n)::ms,(y,p)::ns) ->
	  (match Ord.compare compare x y with
	       0 -> (x,n+p)::(aux (ms,ns))
	     | t when t < 0 -> (y,p)::(aux (((x,n)::ms),ns))
	     | _ -> (x,n)::(aux (ms,((y,p)::ns))))
    in
      ((aux (m1,m2)):t)

  let inter (m1:t) (m2:t) =
    let rec aux = function
	([],_)
      | (_,[]) -> []
      | ((x,n)::ms,(y,p)::ns) -> 
	  (match Ord.compare compare x y with
	       0 -> (x,min n p)::(aux (ms,ns))
	     | t when t < 0 -> aux ((x,n)::ms,ns)
	     | _ -> aux (ms,(y,p)::ns))
    in
      ((aux (m1,m2)):t)

  let diff (m1:t) (m2:t) = 
    let rec aux = function
	(m,[]) -> m
      | ([],_) -> []
      | ((x,n)::ms,(y,p)::ns) ->
	  (match Ord.compare compare x y with
	       0 -> 
		 if p >= n then aux (ms,ns) 
		 else (x,n-p)::(aux (ms,ns))
	     | t when t < 0 -> aux ((x,n)::ms,ns)
	     | _ -> (x,n)::(aux (ms,(y,p)::ns)))
    in 
      ((aux (m1,m2)):t)

  let equal m1 m2 = (compare m1 m2 = 0)

  let subset (m1:t) (m2:t) =
    let rec aux = function
	[],_ -> true
      | _,[] -> false
      | ((x,n)::ms,(y,p)::ns) ->
	  (match Ord.compare compare x y with
	       0 -> 
		 if n <= p then aux (ms,ns) 
		 else false
	     | t when t < 0 -> aux ((x,n)::ms,ns)
	     | _ -> false)
    in
      aux (m1,m2)

  let iter f (m:t) = List.iter (function (x,n) -> f x n) m

  let fold f (m:t) a = List.fold_left (fun a (x,n) -> f x n a) a m

  let multifold f (m:t) a =
    let rec repeat f x a = function
	0 -> a
      | n -> repeat f x (f x a) (n-1)
    in
      List.fold_left (fun a (x,n) -> repeat f x a n) a m

  let map f (m:t) = List.fold_left (fun mset (x,n) -> add (f x) n mset) empty m

  let duplicate p m = 
    let p = max 1 p in
      List.map (function (x,n) -> (x,n*p)) m

  let for_all p (m:t) = List.for_all (function (x,n) -> p x n) m

  let exists p (m:t) = List.exists (function (x,n) -> p x n) m

  let filter p (m:t) = ((List.filter (function (x,n) -> p x n) m):t)

  let partition p (m:t) = ((List.partition (function (x,n) -> p x n) m):t*t)

  let cardinal (m:t) = List.fold_left (fun n (x,m) -> n+m) 0 m

  let elements (m:t) =
    let rec repeat x = function
	0 -> []
      | n -> x::(repeat x (n-1))
    in
    let rec aux = function
	[] -> []
      | (x,n)::tail -> (repeat x n)@(aux tail)
    in
      aux m

  let elements_packed (m:t) = m

  let rec min_elt = function
      ([]:t) -> raise Not_found
    | [x,_] -> x
    | _::tail -> min_elt tail

  let max_elt = function
      ([]:t) -> raise Not_found
    | (x,_)::_ -> x

  let choose = max_elt

  let rec of_list = function
      [] -> empty
    | (x,n)::xs ->
	if n > 0 then add x n (of_list xs)
	else of_list xs
end
