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
open Agent

let max_rate = ref 100  

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


