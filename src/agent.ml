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

let max_rate = ref 100  

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
    | AgentRef(s),AgentRef(t) -> Pervasives.compare s t
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
			      let compare = Pervasives.compare
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

(* donne l'arité d'un processus en forme standard *)
let arity p =
  let check_pos n = if n < 0 then failwith "arity: check_pos" else n 
  and check_neg n = if n > 0 then failwith "arity: check_pos" else n in
  let rec aux = function
      Abs(p) -> (check_pos (aux p)) + 1
    | Conc(_,p) -> (check_neg (aux p)) - 1
    | Nu(p) -> aux p
    | Apply(p,n) -> (check_pos ((aux p) - 1))
    | AgentRef(s) -> failwith "arity: AgentRef is not a standard form"
    | _ -> 0
  in
    aux p
;;

(* absify p n gives \x1...\xn.p *)
let rec absify p = function
    0 -> p
  | n -> absify (Abs(p)) (n-1)
;;

(* nuify p n gives ^x1...^xn.p *)
let rec nuify p = function
    0 -> p
  | n -> nuify (Nu(p)) (n-1)
;;

(* concrefy n [v1;...;vm] p gives ^x1...^xn[v1]...[vm]p *)
let concrefy n vs p =
  nuify (List.fold_right (fun v p -> Conc(v,p)) vs p) n
;;

(* unfold_abstraction env lvl p n *)
let rec unfold_abstraction env lvl p = function
    0 -> p
  | n ->
      (match p with
	   Abs(p) -> unfold_abstraction env (lvl+1) p (n-1)
	 | AgentRef(s) -> (*unfold_abstraction env lvl (env#get_agent lvl s) n*)
	     unfold_abstraction env lvl (env#get_agent lvl s) n
	 | Apply(p,m) ->
	     let p' = unfold_abstraction env lvl p 1 in
	     let p'' = substitute_agent (function n -> if Name.is_zero n then m else Name.pred n) p' in
	       unfold_abstraction env lvl p'' n
	 | _ -> failwith "unfold_abstraction")

(* return (n,q) when p = \x1...\xn.q *)
let rec split_abstraction env lvl = function
    Abs(p) -> let (n,q) = split_abstraction env (lvl+1) p in (n+1,q)
  | Apply(p,m) -> 
      let p' = unfold_abstraction env lvl p 1 in
      let p'' = substitute_agent (function n -> if Name.is_zero n then m else Name.pred n) p' in
	split_abstraction env lvl p''
  | AgentRef(s) -> (*split_abstraction env lvl (env#get_agent lvl s) *)
      split_abstraction env lvl (env#get_agent lvl s)
  | p -> (0,p)

(* return (p,x1..xn,q) when p = ^y1...^yp[x1]...[xn].q *)
(* ^ and [] can be mixed *)
let rec split_concretion env lvl = function
    Conc(x,p) -> let (n,l,q) = split_concretion env lvl p in (n,(Name.plus n x)::l,q)
  | Nu(p) -> 
      (let (n,l,q) = split_concretion env (lvl+1) p in
	 match l with 
	     [] -> (0,[],Nu(p))
	   | _ -> (n+1,l,q))
  | AgentRef(s) -> (*split_concretion env lvl (env#get_agent lvl s)*)
      split_concretion env lvl (env#get_agent lvl s)
  | Apply(p,m) ->
      let p = unfold_abstraction env lvl p 1 in
      let p' = substitute_agent (function n -> if Name.is_zero n then m else Name.pred n) p in
	split_concretion env lvl p'
  | p -> (0,[],p)

let rec split_nu env lvl = function
    Nu(p) -> let (n,q) = split_nu env (lvl+1) p in (n+1,q)
  | AgentRef(s) -> (*split_nu env lvl (env#get_agent lvl s)*)
      split_nu env lvl (env#get_agent lvl s)
  | Apply(p,m) ->
      let p = unfold_abstraction env lvl p 1 in
      let p' = substitute_agent (function n -> if Name.is_zero n then m else Name.pred n) p in
	split_nu env lvl p'
  | p -> (0,p)


let simpl_par ps =
  let rec simpl_parallel ps = 
    AgentMultiset.fold (fun p n (ps,c) -> 
			  match p with
			      Nil -> (ps,c)
			    | Parallel(qs) -> 
				let (qs,d) = simpl_parallel qs in
				  (AgentMultiset.union ps (AgentMultiset.duplicate n qs),c+n*d)
			    | p -> 
				(AgentMultiset.add p n ps,c+n)) ps (AgentMultiset.empty,0)
  in
    match (simpl_parallel ps) with
	(_,0) -> Nil
      | (_,1) ->
	  (match AgentMultiset.elements ps with
	       [x] -> x
	     | _ -> failwith "simpl_par: impossible")
      | (ps,_) -> Parallel(ps)
  
(* calcule la forme standard d'un agent *)
let rec standard_form env lvl = function
    Abs(p) -> Abs(standard_form env (lvl+1) p)
  | Conc(n,p) -> Conc(n,standard_form env lvl p)
  | Nu(p) ->
      let beta_swap = substitute_agent 
			(function n -> 
			   if Name.is_zero n then Name.succ n
			   else
			     if Name.is_zero (Name.pred n) then Name.pred n
			     else n) in
	(match (standard_form env (lvl+1) p) with
	     Abs(q) -> Abs(standard_form env (lvl+1) (Nu(beta_swap q)))
	   | Conc(n,q) ->
	       if Name.is_zero n then Nu(Conc(n,q))
	       else Conc(Name.pred n,standard_form env lvl (Nu(q)))
	   | Nu(Conc(n,q)) ->
	       if Name.is_zero n then Nu(standard_form env (lvl+1) (Conc(Name.zero,Nu(beta_swap q))))
	       else Nu(Nu(Conc(n,q)))
	   | Nil -> Nil
	   | q -> 
	       (try
		  let q = substitute_agent (function n -> Name.pred n) q 
		  in q
		with
		    e -> Nu(q)))
  | Sum(ps) ->
      let rec simpl_sum ps =
	AgentMultiset.fold (fun p n (ps,c) -> 
			      match (standard_form env lvl p) with
				  Nil -> (ps,c)
				| Sum(qs) -> 
				    let (qs,d) = simpl_sum qs in
				      (AgentMultiset.union ps (AgentMultiset.duplicate n qs),c+n*d)
				| p -> (AgentMultiset.add p n ps,c+n)) ps (AgentMultiset.empty,0)
      in
	(match simpl_sum ps with
	     (_,0) -> Nil
	   | (x,1) -> 
	       (match AgentMultiset.elements x with
		    [x] -> x
		  | _ -> failwith "standard_form: impossible")
	   | (xs,_) -> Sum(xs))
  | Parallel(ps) ->
      let rec simpl_parallel ps = 
	AgentMultiset.fold (fun p n (ps,c,mi,ma) -> 
			      match (standard_form env lvl p) with
				  Nil -> (ps,c,mi,ma)
				| Parallel(qs) -> 
				    let (qs,d,mi',ma') = simpl_parallel qs in
				      (AgentMultiset.union ps (AgentMultiset.duplicate n qs),c+n*d,min mi mi',max ma ma')
				| p -> 
				    let ar = arity p in
				      (AgentMultiset.add p n ps,c+n,min mi ar,max ma ar)) ps (AgentMultiset.empty,0,0,0)
      in
	(match (simpl_parallel ps) with
	     (_,0,_,_) -> Nil
	   | (x,1,_,_) ->
	       (match AgentMultiset.elements x with
		    [x] -> x
		  | _ -> failwith "standard_form: impossible")
	   | (xs,_,mina,maxa) -> 
		 if (mina < 0) && (maxa <= 0) then
		   begin
		     let (n,v,ps) =
		       AgentMultiset.multifold
			 (fun p (n,v,ps) ->
			    let (m,w,q) = split_concretion env lvl (substitute_agent (Name.plus n) p) in
			    let ps' = 
			      if (q = Nil) then (AgentMultiset.map (substitute_agent (Name.plus m)) ps) 
			      else AgentMultiset.add q 1 (AgentMultiset.map (substitute_agent (Name.plus m)) ps)
			    in
			    let v' = List.map (Name.plus m) v in
			      (n+m,w@v',ps')) xs (0,[],AgentMultiset.empty)
			 (* 
			    List.fold_left (fun (n,v,ps) p ->
			    let (m,w,q) = split_concretion (substitute_agent (Name.plus n) p) in
			    let ps' = AgentMultiset.add q 1 (AgentMultiset.map (substitute_agent (Name.plus m)) ps) in
			    let v' = List.map (Name.plus m) v in
			    (m+n,w@v',ps')) (0,[],AgentMultiset.empty) (AgentMultiset.elements xs)
			 *)
		     in
		       concrefy n v (standard_form env lvl (Parallel(ps)))
		   end
		 else 
		   if (mina >= 0) && (maxa > 0) then
		     begin
		       let (n,ps) = 
			 AgentMultiset.multifold
			   (fun p (n,ps) ->
			      let (m,q) = split_abstraction env lvl (substitute_agent (Name.plus n) p) in
			      let ps' = 
				(if q = Nil then (AgentMultiset.map (substitute_agent (Name.plus m)) ps)
				 else AgentMultiset.add q 1 (AgentMultiset.map (substitute_agent (Name.plus m)) ps)) 
			      in
				(n+m,ps')) xs (0,AgentMultiset.empty)
			   (*
			     List.fold_left
			     (fun (n,ps) p ->
			     let (m,q) = split_abstraction (substitute_agent (Name.plus n) p) in
			     let ps' = AgentMultiset.add q 1 (AgentMultiset.map (substitute_agent (Name.plus m)) ps) in
			     (n+m,ps')) (0,AgentMultiset.empty) (AgentMultiset.elements xs)
			   *)
		       in
			 absify (standard_form env lvl (Parallel(ps))) n
		     end
		   else
		     begin
		       let (n,ps) =
			 AgentMultiset.multifold
			   (fun p (n,ps) ->
			    let (m,q) = split_nu env lvl (substitute_agent (Name.plus n) p) in
			    let ps' = 
			      if (q = Nil) then (AgentMultiset.map (substitute_agent (Name.plus m)) ps) 
			      else AgentMultiset.add q 1 (AgentMultiset.map (substitute_agent (Name.plus m)) ps)
			    in
			      (n+m,ps')) xs (0,AgentMultiset.empty)
		       in
			 nuify (simpl_par ps) n
		     end)
  | AgentRef(s) -> (*standard_form env lvl (env#get_agent lvl s)*)
      standard_form env lvl (env#get_agent lvl s)
  | Apply(p,m) -> 
      let p' = unfold_abstraction env lvl p 1 in
      let p'' = substitute_agent (function n -> if Name.is_zero n then m else Name.pred n) p' in
	standard_form env lvl p''
  | Match(n,m,p) when Name.compare n m = 0 -> standard_form env lvl p
  | p -> p

(* assume - that f and c are in standard form *)
(*        - that f is an abstraction          *)
(*        - that c is a concretion            *)
(*        - and they have the same arity      *)
let pseudo_application env lvl f c =
  let (n,p) = split_abstraction env lvl f
  and (m,vs,q) = split_concretion env lvl c in
  let p = substitute_agent (Name.apply_substitution n vs (Name.plus m)) p in
    nuify (Parallel(AgentMultiset.of_list [(p,1);(q,1)])) m

module NameDist = Distinctions.Make(Name)(NameCond)

module Commitments = Set.Make(struct
				type t = NameCond.t * action * agent
				let compare (c,a,p) (c',a',p') =
				  match compare_action a a' with
				      0 ->
					(match NameCond.compare c c' with
					     0 -> compare p p'					       
					   | t -> t)
				    | t -> t
			      end)

module AgentMap = Map.Make(struct
			     type t = int * agent
			     let compare (n,p) (m,q) =
			       match Pervasives.compare n m with
				   0 -> compare p q
				 | t -> t
			   end)

let strong_tbl = ref AgentMap.empty
let weak_tbl = ref AgentMap.empty

let buffer_counter = ref 0
let buffer_rate = ref (!max_rate)
let bufferize = ref (!buffer_rate = !max_rate)

let update_bufferize () =
  buffer_counter := !buffer_counter + !buffer_rate;
  if !buffer_counter >= !max_rate then
    begin
      buffer_counter := !buffer_counter - !max_rate;
      bufferize := true
    end
  else
    bufferize := false

let clear hashtbl = hashtbl := AgentMap.empty

let clean_buffer () =
  clear strong_tbl;
  clear weak_tbl

let buffer_switch n =
  buffer_rate := n;
  buffer_counter := 0;
  bufferize := (n = !max_rate);
  clean_buffer ()

let set_maxrate n = 
  let rate = int_of_float (((float_of_int !buffer_rate) /. (float_of_int !max_rate)) *. (float_of_int n)) in
    max_rate := n;
    buffer_switch rate

let lookup hashtbl ((lvl,p) as key) f =
  (try
     AgentMap.find key (!hashtbl)
   with
       Not_found -> 
	 let info = f key in
	   if !bufferize then
	     hashtbl := AgentMap.add key info (!hashtbl);
	   update_bufferize ();
	   info)

let sub_action p = function
    Tau -> Tau
  | Input(n) -> Input(Name.plus (-p) n)
  | Output(n) -> Output(Name.plus (-p) n)

let rec conditionnal_product p l1 l2 =
  List.fold_left (fun prod a -> (List.fold_left (fun pr_a b -> if (p a b) then (a,b)::pr_a else pr_a) [] l2)@prod) [] l1

let compute_comm_rule env lvl agents input output =
  let n = Array.length agents in
  let rec aux1 i =
    let rec aux2 j =
      let rec aux3 k =
	if k < n then
	  if (k != i) && (k != j) then
	    agents.(k)::(aux3 (k+1))
	  else
	    let (p,i) = agents.(k) in
	      if i > 1 then (p,i-1)::(aux3 (k+1))
	      else (aux3 (k+1))
	else []
      in
	if j < n then
	  if (j != i) then
	    let others = aux3 0 in
	      List.fold_left
		(fun comms ((_,(condM,Input(x),f)),(_,(condN,Output(y),c))) ->
		   Commitments.add
		     (NameCond.add (x,y) (NameCond.union condM condN),
		      Tau,
		      standard_form env lvl 
			(Parallel(AgentMultiset.of_list (((pseudo_application env lvl f c),1)::others)))) comms)
		(aux2 (j+1))
		(conditionnal_product (fun (ari,_) (aro,_) -> ari = -aro) input.(i) output.(j))
	  else aux2 (j+1)
	else Commitments.empty
    in
      if i < n then Commitments.union (aux2 0) (aux1 (i+1))
      else Commitments.empty
  in
    aux1 0

let compute_par_rule env lvl agents comm =
  let n = Array.length agents in
  let rec aux1 i =
    let rec aux2 k =
      if k < n then 
	if (k != i) then agents.(k)::(aux2 (k+1))
	else
	  let (p,i) = agents.(k) in
	    if i > 1 then ((p,i-1)::(aux2 (k+1)))
	    else aux2 (k+1)
      else []
    in
      if i < n then
	let others = aux2 0 in
	  List.fold_left 
	    (fun comms (_,(c,a,p)) -> 
	       Commitments.add 
		 (c,a,standard_form env lvl (Parallel(AgentMultiset.of_list ((p,1)::others))))
		 comms)
	    (aux1 (i+1))
	    comm.(i)
      else Commitments.empty
  in
    aux1 0


(* compute the strong conditionnal open commitments of a process in standard form *)
let rec commitments env lvl p = 
  lookup strong_tbl (lvl,p) 
    (function (lvl,p) ->
       match p with
	   Prefix(a,p) -> (* PRE rule *) 
	     Commitments.singleton (NameCond.empty,a,standard_form env lvl p)
	 | Sum(ps) ->(* SUM rule *)
	     AgentMultiset.fold 
	     (fun p n comms ->
		Commitments.union (commitments env lvl (standard_form env lvl p)) comms) ps Commitments.empty
	 | Parallel(ps) -> (* PAR rules *)
	     let ps = AgentMultiset.elements_packed ps in
	     let comm_ps = List.map 
			     (function (p,n) -> 
				let comm_p = commitments env lvl (standard_form env lvl p) in
				  Commitments.fold (fun ((c,a,p') as comm) comms ->
						      let ar = arity p' in
							(ar,comm)::comms) comm_p []) ps in
	     let input_comms = Array.of_list 
				 (List.map 
				    (function comm_p -> 
				       List.filter 
				       (function (n,(_,Input(_),_)) -> (n >= 0) | _ -> false) comm_p) comm_ps) in
	     let output_comms = Array.of_list 
				  (List.map 
				     (function comm_p -> 
					List.filter 
					(function (n,(_,Output(_),_)) -> (n <= 0) | _ -> false) comm_p) comm_ps) in
	     let agents = Array.of_list ps in
	       Commitments.union 
		 (compute_par_rule env lvl agents (Array.of_list comm_ps)) 
		 (compute_comm_rule env lvl agents input_comms output_comms)
	 | Nu(p) -> (* RES rule *)
	     let comm_p = commitments env (lvl+1) (standard_form env (lvl+1) p) in
	       Commitments.fold 
		 (fun (cond,alpha,p') comms ->
		    try
		      let alpha' = sub_action 1 alpha in
		      let cond' = NameCond.map Name.pred cond in
			Commitments.add (cond',alpha',standard_form env lvl (Nu(p'))) comms
		    with
			_ -> comms) comm_p Commitments.empty
	 | Match(n,m,p) -> (* MATCH rule *)
	     let comm_p = commitments env lvl (standard_form env lvl p) in
	       Commitments.fold 
		 (fun (cond,alpha,p') comms -> 
		    Commitments.add (NameCond.add (n,m) cond,alpha,p') comms) comm_p Commitments.empty
	 | _ -> Commitments.empty)

(* compute commitments generated by a set of commitment *)
(* according to weak commitment definition *)
let one_step env lvl comm =
  Commitments.fold (fun (cond,alpha,p) comms ->
		      let ar_p = arity p in
			if ar_p = 0 then
			  (* p is a process *)
			  begin
			    let comm_p = commitments env lvl p in
			    let step_comm_p = Commitments.fold
						(fun (c,a,q) comms -> 
						   match a with
						       Tau -> Commitments.add (NameCond.union cond c,alpha,q) comms
						     | Input(n)
						     | Output(n) -> 
							 if alpha = Tau then
							   Commitments.add (NameCond.union cond c,a,q) comms
							 else comms)
						comm_p Commitments.empty in
			      Commitments.union step_comm_p comms
			  end
			else
			  if alpha <> Tau then
			    if ar_p > 0 then
			      begin
				let (n,p) = split_abstraction env lvl p in
				let comm_p = commitments env lvl p in
				let step_comm_p = Commitments.fold
						    (fun (c,a,q) comms ->
						       match a with
							   Tau ->
							     (try
								Commitments.add (NameCond.union (NameCond.map (Name.plus (-n)) c) cond,alpha,absify q n) comms
							      with
								  _ -> comms)
							 | _ -> comms) comm_p Commitments.empty in
				  Commitments.union step_comm_p comms
			      end
			    else
			      begin
				let (n,vs,p) = split_concretion env lvl p in
				let comm_p = commitments env lvl p in
				let step_comm_p = Commitments.fold
						    (fun (c,a,q) comms ->
						       match a with
							   Tau ->
							     (try
								Commitments.add (NameCond.union (NameCond.map (Name.plus (-n)) c) cond,alpha,concrefy n vs q) comms
							      with
								  _ -> comms)
							 | _ -> comms) comm_p Commitments.empty in
				  Commitments.union step_comm_p comms
			      end
			  else comms) comm Commitments.empty

(* compute the weak closure of a set of commitments *)
let closure env lvl comm =
  let rec aux c d =
    let d' = one_step env lvl d in
    let c' = Commitments.union c d' in
      if Commitments.cardinal c = Commitments.cardinal c' then c
      else aux c' d'
  in
    aux comm comm

(* initial weak commitment of an agent *)
let init_weak_comm env lvl p = Commitments.singleton (NameCond.empty,Tau,standard_form env lvl p)

let weak_commitments env lvl p = 
  lookup weak_tbl (lvl,p) 
  (function (lvl,p) -> closure env lvl (init_weak_comm env lvl p))

module Bisimulations = Set.Make(struct 
				  type t = agent * agent * NameDist.t
				  let compare (p,q,d) (p',q',d') =
				    match (NameDist.compare d d') with
					0 ->
					  (match compare p p' with
					       0 -> compare q q'
					     | t -> t)
				      | t -> t
				end)

exception FoundB of Bisimulations.t

let bisim_add bisim p q d b =
  let (p,q) = 
    if bisim then
      (match compare p q with
	   t when t <= 0 -> (p,q)
	 | _ -> (q,p))
    else (p,q)
  in
    Bisimulations.add (p,q,d) b

let bisim_exists bisim p q d r =
  let (p,q) = 
    if bisim then
      (match compare p q with
	   t when t <= 0 -> (p,q)
	 | _ -> (q,p))
    else (p,q)
  in
    Bisimulations.exists 
      (function (p',q',d') -> 
	 (compare p p' = 0) && 
	 (compare q q' = 0) &&
	 (NameDist.subset d' d)) r

type 'a transition = Strong of 'a | Weak of 'a

module ExtBisimulations = Set.Make(struct 
				     type t = agent * agent * NameDist.t * ((((action transition) * agent) option list) * (((action transition) * agent) option list))
				     let compare (p,q,d,_) (p',q',d',_) =
				       match (NameDist.compare d d') with
					   0 ->
					     (match compare p p' with
						  0 -> compare q q'
						| t -> t)
					 | t -> t
				   end)

let extbisim_add bisim p q d tp tq b =
  let (p,q,tp,tq) = 
    if bisim then
      (match compare p q with
	   t when t <= 0 -> (p,q,tp,tq)
	 | _ -> (q,p,tq,tp))
    else (p,q,tp,tq)
  in
    ExtBisimulations.add (p,q,d,(tp,tq)) b

let not_bisim = ref ExtBisimulations.empty;;

let bisim_empty bisim p q d tp tq =
  not_bisim := extbisim_add bisim p q d tp tq (!not_bisim);
  Bisimulations.empty

let bisim_neq bisim p q d =
  let tp = ref [] and tq = ref [] in
  let (p,q,rev) = 
    if bisim then
      (match compare p q with
	   t when t <= 0 -> (p,q,false)
	 | _ -> (q,p,true))
    else (p,q,false)
  in
  let booleen = 
    ExtBisimulations.exists 
      (function (p',q',d',(tp',tq')) ->
	 tp := tp';
	 tq := tq';
	 (compare p p' = 0) &&
	 (compare q q' = 0) &&
	 (NameDist.subset d d')) (!not_bisim) in
    if rev then  (booleen,(!tq,!tp)) else (booleen,(!tp,!tq))

(*
  let string_of_var lvl n = Name.to_string lvl n

  let string_of_action lvl = function
  Tau -> "t"
  | Input(n) -> string_of_var lvl n
  | Output(n) -> "'"^(string_of_var lvl n)
  
  let rec string_of_agent lvl = function
    Nil -> "0"
  | Prefix(a,p) -> 
  (string_of_action lvl a)^"."^(string_of_agent lvl p)
  | Conc(n,p) -> ("["^(string_of_var lvl n)^"]"^(string_of_agent lvl p))
  | Abs(p) ->
  let rec aux lvl = function
  Abs(q) -> ","^(string_of_var (lvl+1) Name.zero)^(aux (lvl+1) q)
  | q -> ")"^(string_of_agent lvl q)
  in
  ("(\\"^(string_of_var (lvl+1) (Name.zero))^(aux (lvl+1) p))
  | Nu(p) -> 
  let rec aux lvl = function
  Nu(q) -> ","^(string_of_var (lvl+1) Name.zero)^(aux (lvl+1) q)
  | q -> ")"^(string_of_agent lvl q)
  in
  ("(^"^(string_of_var (lvl+1) (Name.zero))^(aux (lvl+1) p))
  | Match(n,m,p) -> ("["^(string_of_var lvl n)^"="^(string_of_var lvl m)^"]"^(string_of_agent lvl p))
  | AgentRef(s) -> s
  | Apply(p,n) -> (string_of_agent lvl p)^" "^(string_of_var lvl n)
  | Sum(ps) -> 
  let str = (List.fold_left
  (fun str p -> 
  let strp = string_of_agent lvl p in
  (str^(if str = "" then "" else " + ")^strp)) "" (AgentMultiset.elements ps)) 
  in "("^str^")"
  | Parallel(ps) ->
  let str = (List.fold_left
  (fun str p -> 
  let strp = string_of_agent lvl p in
  (str^(if str = "" then "" else " | ")^strp)) "" (AgentMultiset.elements ps)) 
  in "("^str^")"
  
  let print_action a = Format.print_string (string_of_action 0 a) 
  let print_agent p = Format.print_string (string_of_agent 0 p)
*)

(*
class ['a] arbreMutable (elem:'a) (eq:'a->'a->bool) =
  let indente n = print_string (String.make n ' ') in
  let rec last = function 
      [] -> []
    | [x] -> [x]
    | _::xs -> last xs in
  let last x = x in 
object(self)
  val mutable sons = []
  val mutable father = None
  method setFather f = father <- Some(f)
  method newSon son = 
    try
      self#getSon son 
    with
	Not_found ->
	  let fils = new arbreMutable son eq in
	    fils#setFather (self:>'a arbreMutable);
	    sons <- fils::sons;
	    fils
  method removeSon son =
    sons <- List.filter (function fils -> (not (eq (fils#getElem) (son))) || (not (fils#isLeaf))) sons
  method private getSon son =
    List.find (function fils -> eq (fils#getElem) son) sons
  method getSons = sons
  method getElem = elem
  method getFather = father
  method print toString = self#pp toString false 0
  method pp toString b n =
    if not b then indente n;
    let elemStr = if self#isRoot then "" else (toString elem) in
    let elemLen = String.length elemStr in
      print_string elemStr;
      indente 1;
      if self#isLeaf then
	print_newline()
      else
	ignore (List.fold_left (fun b fils -> fils#pp toString b (n+1+elemLen);false) true (last sons))
  method isLeaf =
    match sons with
	[] -> true
      | _ -> false
  method isRoot =
    match father with
	None -> true
      | _ -> false
  method clear = 
    sons <- [];
    father <- None;
  method level = 
    match father with
	None -> 0
      | Some(f) -> 1 + f#level
  method length =
    1+(List.fold_left (fun l f -> max l f#length) 0 sons)
end


(*
  class ['a] trace_keep =
  object(self)
  val action_stack = Stack.create ()
  method push_action (a:'a) = Stack.push a action_stack
  method pop_action = ignore (Stack.pop action_stack)
  method clear = 
  Stack.clear action_stack;
  method print (pp_action:'a->unit) =
  let exec_action = ref [Format.print_newline] in
  Stack.iter (function a -> exec_action := (function () -> pp_action a;Format.print_string " ")::(!exec_action)) action_stack;
  List.iter (function f -> f ()) (!exec_action)
  method enter = self
  end	
*)

let eq_trace (alpha,p) (beta,q) = (compare_action alpha beta = 0) && (compare p q = 0)

let get_traces print ap aq =
  let rec aux aqs (tp,tq) = function
      [] -> [],[]
    | ap::aps ->
	let (alpha,p') = ap#getElem in
	let aqs' = List.filter (function aq -> 
				  let (beta,q') = aq#getElem in (compare_action alpha beta=0)) aqs in
	  if aqs' = [] then ((alpha,p')::tp,None::tq)
	  else
	    begin
	      let l = List.map (function aq' -> 
				  let (beta,q') = aq'#getElem in
				    aux aq'#getSons ((alpha,p')::tp,(Some(beta,q'))::tq) ap#getSons) aqs' in
		if List.exists (function x -> x = ([],[])) l then
		  aux aqs (tp,tq) aps
		else
		  List.hd l
	    end
  in
    aux aq#getSons ([],[]) ap#getSons

let trace_left_strong = new arbreMutable (Tau,Nil) eq_trace
(*
  let trace_left_weak = new arbreMutable (Tau,Nil) eq_trace
  let trace_right_strong = new arbreMutable (Tau,Nil) eq_trace
*)
let trace_right_weak = new arbreMutable (Tau,Nil) eq_trace
*)

(* p and q must be in standard form *)
(* bisim is a flag that indicates if we check simulation or bisimulation *)
let rec add bisim env s_comm w_comm (* trace_p_strong trace_q_weak *) (* trace_p_weak trace_q_strong *) p q d r =
  let (b,(tp,tq)) = bisim_neq bisim p q d in
  if b then 
    begin
(*
      Format.print_string "exit 1";Format.print_newline();
*)
      ((bisim_empty bisim p q d tp tq),(tp,tq))
    end
  else
    (* the original code was the commented one *)
    (* but in case that there already exist a d' such that d' is a subset of d and (p,q,d') in r *)
    (* then there is no need to add (p,q,d) to r *)
    (* if (bisim_exists p q d r) || (compare p q = 0) then bisim_add bisim p q d r *)
    if (bisim_exists bisim p q d r) then 
      begin
(*
	Format.print_string "exit 2";Format.print_newline();
*)
	(r,([],[]))
      end
    else 
      if (compare p q = 0) then 
	begin
(*
	  Format.print_string "exit 3";Format.print_newline();
*)
	  (bisim_add bisim p q d r,([],[]))
	end
      else
	let ar_p = arity p and ar_q = arity q in
	  if (ar_p = 0) && (ar_q = 0) then
	    (* p and q are processes *)
	    begin
	      let filtre comm = Commitments.filter (function (m,_,_) -> NameDist.respects m d) comm in
	      let pc = filtre (s_comm env 0 p)
	      and qcw = filtre (w_comm env 0 q) in
		let (r',(tp,tq)) = matches bisim env s_comm w_comm (* trace_p_strong trace_q_weak *) (* trace_p_weak trace_q_strong *) pc qcw d (bisim_add bisim p q d r) in
		  if Bisimulations.is_empty r' then ((bisim_empty bisim p q d tp tq),(tp,tq))
		  else
		    if bisim then
		      begin
			let qc = (if s_comm == w_comm then qcw else filtre (s_comm env 0 q))
			and pcw = (if s_comm == w_comm then pc else filtre (w_comm env 0 p)) in
			let (r'',(tq,tp)) = matches bisim env s_comm w_comm (* trace_q_strong trace_p_weak *) (* trace_q_weak trace_p_strong *) qc pcw d r' in
			  if Bisimulations.is_empty r'' then ((bisim_empty bisim p q d tp tq),(tp,tq))
			  else
			    begin
			      (r'',(tp,tq))
			    end
		      end
		    else (r',(tp,tq))
	    end
	  else
	    if (ar_p = ar_q) then
	      if ar_p > 0 then
		(* p and q are abstractions of the same arity *)
		begin
		  let (np,p') = split_abstraction env 0 p 
		  and (nq,q') = split_abstraction env 0 q in
		    assert (np = nq);
		    let fnpq = NameSet.elements (NameSet.union (free_names env p) (free_names env q)) in
		    let freshnames = Name.freshnames np fnpq in
		    let sigma = Name.apply_substitution np freshnames (function n -> n) in
		    let p'' = substitute_agent sigma p' 
		    and q'' = substitute_agent sigma q' in
		      add bisim env s_comm w_comm (* trace_p_strong trace_q_weak *) (* trace_p_weak trace_q_strong *) p'' q'' d (bisim_add bisim p q d r)
		end
	      else
		(* p and q are concretions of the same arity *)
		begin
		  let (np,vp,p') = split_concretion env 0 p 
		  and (nq,vq,q') = split_concretion env 0 q in
		    assert (List.length vp = List.length vq);
		    if (np = nq) then
		      begin
			let fnpq = NameSet.elements (NameSet.union (free_names env p) (free_names env q)) in
			let freshnames = Name.freshnames np fnpq in
			let sigma = Name.apply_substitution np freshnames (function n -> n) in
			let vp' = List.map sigma vp
			and vq' = List.map sigma vq in
			  if vp' = vq' then
			    begin
			      let p'' = substitute_agent sigma p'
			      and q'' = substitute_agent sigma q' in
				(* bugfix : the freshnames must be pairwise distinct *)
			      let d' = NameDist.union (NameDist.prune fnpq d) (NameDist.union (NameDist.pwd freshnames) (NameDist.generate freshnames fnpq)) in
				add bisim env s_comm w_comm (* trace_p_strong trace_q_weak *) (* trace_p_weak trace_q_strong *) p'' q'' d' (bisim_add bisim p q d r)
			    end
			  else 
			    begin
(*
			      Format.print_string "exit 4";Format.print_newline();
*)
			      ((bisim_empty bisim p q d [] []),([],[]))
			    end
		      end
		    else 
		      begin
(*
			Format.print_string "exit 5";Format.print_newline();
*)
			((bisim_empty bisim p q d [] []),([],[]))
		      end
		end
	  else 
	    begin
(*	      Format.print_string "Incompatible arities.";Format.print_newline(); *)
(*
	      Format.print_string "exit 6";Format.print_newline();
*)
	      ((bisim_empty bisim p q d [] []),([],[]))
	    end
and matches bisim env s_comm w_comm (* trace_p_strong trace_q_weak *) (* trace_p_weak trace_q_strong *) p_comm q_comm d  r =
  if Bisimulations.is_empty r then 
    begin
(*      Format.print_string "Bisim empty.";Format.print_newline(); *)
(*
      Format.print_string "exit 7";Format.print_newline();
*)
      (Bisimulations.empty,([],[]))
    end
  else
    if Commitments.is_empty p_comm then 
      begin
(*
	Format.print_string "exit 8";Format.print_newline();
*)
	(r,([],[]))
      end
    else
(*
      if Commitments.is_empty q_comm then 
	begin
	  Bisimulations.empty
	end
      else
*)
	begin
	  let (m,alpha,p) = Commitments.min_elt p_comm in
	  let sigma_m = NameCond.canonical_substitution m in
	  let alpha' = substitute_action sigma_m 0 alpha
	  and p' = substitute_agent sigma_m p 
	  and d' = NameDist.map sigma_m d in
(*
	  let trace_p' = trace_p_strong#newSon (alpha',p') in
*)
	  let tq_head = ref None in
	  let tp_tail = ref [] and tq_tail = ref [] in
	    (try
	       Commitments.iter 
		 (function (n,beta,q) ->
		    if NameCond.implies m n then
		      begin
			if (compare_action alpha' (substitute_action sigma_m 0 beta) = 0) then 
			  begin
			    let q' = substitute_agent sigma_m q in
			      tq_head := Some(Weak(alpha'),q');
			      let (r',(tp',tq')) = add bisim env s_comm w_comm (* trace_p' (trace_q_weak#newSon (alpha',q')) *) (* trace_p_weak trace_q_strong *) p' q' d' r in
				if (Bisimulations.is_empty r') then 
				  begin
				    tp_tail := tp';
				    tq_tail := tq';
				  end
				else 
				  begin
				    (* trace_q_weak#removeSon (alpha',q'); *)
				    raise (FoundB(r'))
				  end
			  end
			else ()
		      end
		    else ()) q_comm;
	       Bisimulations.empty,((Some(Strong(alpha'),p'))::(!tp_tail),(!tq_head)::(!tq_tail))
	     with
		 FoundB(r') -> 
		   (* trace_p_strong#removeSon (alpha',p'); *)
		   matches bisim env s_comm w_comm (* trace_p_strong trace_q_weak *) (* trace_p_weak trace_q_strong *) (Commitments.remove (m,alpha,p) p_comm) q_comm d r')
	end

let clear_all () =
  clear strong_tbl;
  clear weak_tbl;
  not_bisim := ExtBisimulations.empty;
(*
  trace_left_strong#clear;
(*
  trace_left_weak#clear;
  trace_right_strong#clear;
*)
  trace_right_weak#clear
*)
;;

let eq env p q d =
  clear_all ();
  let (res,t) = add true env commitments commitments (* trace_left_strong trace_right_weak *) (* trace_left_weak trace_right_strong *) (standard_form env 0 p) (standard_form env 0 q) d Bisimulations.empty in
    (Bisimulations.cardinal res,res,t)

let weq env p q d =
  clear_all ();
  let (res,t) = add true env commitments weak_commitments (* trace_left_strong trace_right_weak *) (* trace_left_weak trace_right_strong *) (standard_form env 0 p) (standard_form env 0 q) d Bisimulations.empty in
    (Bisimulations.cardinal res,res,t)

let lt env p q d =
  clear_all ();
  let (res,t) = add false env commitments commitments (* trace_left_strong trace_right_weak *) (* trace_left_weak trace_right_strong *) (standard_form env 0 p) (standard_form env 0 q) d Bisimulations.empty in
    (Bisimulations.cardinal res,res,t)

let wlt env p q d =
  clear_all ();
  let (res,t) = add false env commitments weak_commitments (* trace_left_strong trace_right_weak *) (* trace_left_weak trace_right_strong *) (standard_form env 0 p) (standard_form env 0 q) d Bisimulations.empty in
    (Bisimulations.cardinal res,res,t)

let dist_of_list fv =
  let prod =
    List.fold_left (fun p x -> List.fold_left (fun p y -> if (Name.compare x y = 0) then p else (x,y)::p) p fv) [] fv 
  in
    List.fold_left (fun d x -> NameDist.add x d) NameDist.empty prod

let dist_of_lists l l' =
  let prod = 
    List.fold_left (fun p x -> List.fold_left (fun p y -> if (Name.compare x y = 0) then p else (x,y)::p) p l) [] l' 
  in
    List.fold_left (fun d x -> NameDist.add x d) NameDist.empty prod

(* p should be in standard form *)
let concretise env p =
  let ar = arity p in
    if ar = 0 then p
    else
      if ar > 0 then
	begin
	  let (n,p') = split_abstraction env 0 p in
	  let fnp = NameSet.elements (free_names env p) in
	  let freshnames = Name.freshnames n fnp in
	  let sigma = Name.apply_substitution n freshnames (function n -> n) in
	  let p'' = substitute_agent sigma p' in
	    standard_form env 0 p''
	end
      else
	begin
	  let (n,_,p') = split_concretion env 0 p in
	  let fnp = NameSet.elements (free_names env p) in
	  let freshnames = Name.freshnames n fnp in
	  let sigma = Name.apply_substitution n freshnames (function n -> n) in
	  let p'' = substitute_agent sigma p' in
	    standard_form env 0 p''
	end


(* p should be in standard form *)
let next_commitments env p = 
  clear_all();
  commitments env 0 (concretise env p)
