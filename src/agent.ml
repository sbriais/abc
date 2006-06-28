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
module NameCond = Conditions.Make(Name)

let string_compare s t =
  let n = String.length s 
  and m = String.length t 
  in
    match n-m with
      | 0 -> 
	  let i = ref 0 in
	  let r = ref 0 in
	    while (!i < n) && (!r = 0) do
	      r := (Char.code s.[!i]) - (Char.code t.[!i]);
	      incr i
	    done;
	    !r
      | t -> t
	  
(* les trois types d'action possibles *)
type action = Tau
	      | Input of Name.t
	      | Output of Name.t

(* les agents *)
(* l'utilisation des multiensembles permet de gérer l'associativité et la commutativité des constructeurs *)
type agent = Nil
	     | Prefix of action * agent
	     | Conc of Name.t * agent
	     | Abs of agent
	     | Nu of agent
	     | Sum of agent Multiset.multiset
	     | Parallel of agent Multiset.multiset
	     | Match of Name.t * Name.t * agent
	     | AgentRef of string
	     | Apply of agent * Name.t

(* comparaison des actions *)
let compare_action x y =
  match (x,y) with
      Tau,Tau -> 0
    | Tau,_ -> -1
    | _,Tau -> 1
    | Input(n),Input(m) -> Name.compare n m
    | Input(_),_ -> -1
    | _,Input(_) -> 1
    | Output(n),Output(m) -> Name.compare n m
;;

(* comparaison des agents paramétrées par la comparaison sur les multiensembles d'agents *)
(* ceci est donc défini de manière mutuellement récursive *)
let rec compare_agent multiset_cmp x y =
  match (x,y) with
      Nil,Nil -> 0
    | Nil,_ -> -1
    | _,Nil -> 1
    | Prefix(alpha,p),Prefix(beta,q) ->
	(match compare_action alpha beta with
	     0 -> compare_agent multiset_cmp p q
	   | t -> t)
    | Prefix(_),_ -> -1
    | _,Prefix(_) -> 1
    | Conc(n,p),Conc(m,q) ->
	(match Name.compare n m with
	     0 -> compare_agent multiset_cmp p q
	   | t -> t)
    | Conc(_),_ -> -1
    | _,Conc(_) -> 1
    | Abs(p),Abs(q) -> compare_agent multiset_cmp p q
    | Abs(_),_ -> -1
    | _,Abs(_) -> 1
    | Nu(p),Nu(q) -> compare_agent multiset_cmp p q
    | Nu(_),_ -> -1
    | _,Nu(_) -> 1
    | Sum(ps),Sum(qs) -> multiset_cmp ps qs
    | Sum(_),_ -> -1
    | _,Sum(_) -> 1
    | Parallel(ps),Parallel(qs) -> multiset_cmp ps qs
    | Parallel(_),_ -> -1
    | _,Parallel(_) -> 1
    | Match(n1,n2,p),Match(m1,m2,q) ->
	(match Name.compare n1 m1 with
	     0 -> (match Name.compare n2 m2 with
		       0 -> compare_agent multiset_cmp p q
		     | t -> t)
	   | t -> t)
    | Match(_),_ -> -1
    | _,Match(_) -> 1
    | AgentRef(s),AgentRef(t) -> String.compare s t
    | AgentRef(_),_ -> -1
    | _,AgentRef(_) -> 1
    | Apply(p,n),Apply(q,m) -> 
	(match Name.compare n m with
	     0 -> compare_agent multiset_cmp p q
	   | t -> t)

(* on peut maintenant construire le module des multiset d'agents *)
module AgentMultiset = Multiset.Make(struct 
				       type t = agent
				       let compare = compare_agent
				     end)

(* et on finit de définir la comparaison entre agents *)
let compare = compare_agent AgentMultiset.compare

(* on définit le module des ensembles de noms *)
module NameSet = Set.Make(struct
			    type t = Name.t
			    let compare = Name.compare
			  end)

(* substitution des noms dans les actions *)
let substitute_action subst lvl = function
    Tau -> Tau
  | Input(alpha) -> Input(Name.substitute subst lvl alpha)
  | Output(alpha) -> Output(Name.substitute subst lvl alpha)

(* substitution des noms dans les agents *)
let substitute_agent subst p =
  let rec aux lvl = function
      Nil -> Nil
    | Prefix(alpha,p) -> Prefix(substitute_action subst lvl alpha,aux lvl p)
    | Conc(n,p) -> Conc(Name.substitute subst lvl n,aux lvl p)
    | Abs(p) -> Abs(aux (lvl+1) p)
    | Nu(p) -> Nu(aux (lvl+1) p)
    | Sum(ps) -> Sum(AgentMultiset.map (aux lvl) ps)
    | Parallel(ps) -> Parallel(AgentMultiset.map (aux lvl) ps)
    | Match(n,m,p) -> Match(Name.substitute subst lvl n,Name.substitute subst lvl m,aux lvl p)
    | Apply(p,n) -> Apply(aux lvl p,Name.substitute subst lvl n)
    | AgentRef(s) -> AgentRef(s)
  in
    aux 0 p

(* calcule pour placer un lieur en tête *)
(* le nom n sera le nom lié *)
let add_binder n a = substitute_agent (function p -> if Name.compare p n = 0 then Name.zero else Name.succ p) a

exception Not_defined of string

(*
  let get_agent env lvl s =
  (try
  (*
       substitute_agent (Name.plus lvl) (Hashtbl.find env s)
*)
  Hashtbl.find env s (* OPT *)
  with
  Not_found -> raise (Not_defined s))
*)

(* calcule les noms libres d'un agent *)
(* un petit hack pour calculer les noms libres d'un agent nommé *)
module StringSet = Set.Make(struct
			      type t = string
			      let compare = string_compare
			    end)

let free_names env p =
  let rec fn lvl s_set = function
      Nil -> NameSet.empty
    | Prefix(Tau,p) -> fn lvl s_set p
    | Prefix(Input(n),p) 
    | Prefix(Output(n),p)
    | Conc(n,p) 
    | Apply(p,n) ->
	if Name.is_free lvl n then NameSet.add (Name.freename lvl n) (fn lvl s_set p)
	else fn lvl s_set p
    | Abs(p)
    | Nu(p) -> fn (lvl+1) s_set p
    | Sum(ps)
    | Parallel(ps) ->
	AgentMultiset.fold (fun p _ fns -> NameSet.union (fn lvl s_set p) fns) ps NameSet.empty
    | Match(n,m,p) ->
	if Name.is_free lvl n then
	  NameSet.add (Name.freename lvl n) 
	    (if Name.is_free lvl m then
	       NameSet.add (Name.freename lvl m) (fn lvl s_set p)
	     else
	       fn lvl s_set p)
	else
	  (if Name.is_free lvl m then
	     NameSet.add (Name.freename lvl m) (fn lvl s_set p)
	   else
	     fn lvl s_set p)
    | AgentRef(s) -> 
	(*
	  if StringSet.mem s s_set then NameSet.empty
	  else fn lvl (StringSet.add s s_set) (env#get_agent lvl s)
	*)
	NameSet.empty (* OPT *)
  in
    fn 0 StringSet.empty p

class environment =
object(self)
  val agent_tbl = Hashtbl.create 10
  method add_agent s (a:agent) =
    Hashtbl.replace agent_tbl s a
  method get_agent (lvl:int) s =
    (try
       Hashtbl.find agent_tbl s
     with
	 Not_found -> raise (Not_defined s))
  method reset = Hashtbl.clear agent_tbl
end

(* calcul des noms libres (cas général) *)
let real_free_names env p =
  let rec fn lvl s_set = function
      Nil -> NameSet.empty
    | Prefix(Tau,p) -> fn lvl s_set p
    | Prefix(Input(n),p) 
    | Prefix(Output(n),p)
    | Conc(n,p) 
    | Apply(p,n) ->
	if Name.is_free lvl n then NameSet.add (Name.freename lvl n) (fn lvl s_set p)
	else fn lvl s_set p
    | Abs(p)
    | Nu(p) -> fn (lvl+1) s_set p
    | Sum(ps)
    | Parallel(ps) ->
	AgentMultiset.fold (fun p _ fns -> NameSet.union (fn lvl s_set p) fns) ps NameSet.empty
    | Match(n,m,p) ->
	if Name.is_free lvl n then
	  NameSet.add (Name.freename lvl n) 
	    (if Name.is_free lvl m then
	       NameSet.add (Name.freename lvl m) (fn lvl s_set p)
	     else
	       fn lvl s_set p)
	else
	  (if Name.is_free lvl m then
	     NameSet.add (Name.freename lvl m) (fn lvl s_set p)
	   else
	     fn lvl s_set p)
    | AgentRef(s) -> 
	if StringSet.mem s s_set then NameSet.empty
	else fn lvl (StringSet.add s s_set) (env#get_agent lvl s)
  in
    fn 0 StringSet.empty p

let set_of_list l =
  List.fold_left (fun s x -> NameSet.add x s) NameSet.empty l

module AgentMap = Map.Make(struct
			     type t = int * agent
			     let compare (n,p) (m,q) =
			       match (n-m)-(m-n) with
				   0 -> compare p q
				 | t -> t
			   end)




