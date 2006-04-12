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
open Semantic

module NameDist = Distinctions.Make(Name)(NameCond)

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
  
  let print_action a = !Formatter.format#print_string (string_of_action 0 a) 
  let print_agent p = !Formatter.format#print_string (string_of_agent 0 p)
*)

(* p and q must be in standard form *)
(* bisim is a flag that indicates if we check simulation or bisimulation *)
let rec add bisim env s_comm w_comm (* trace_p_strong trace_q_weak *) (* trace_p_weak trace_q_strong *) p q d r =
  let (b,(tp,tq)) = bisim_neq bisim p q d in
  if b then 
    begin
(*
      !Formatter.format#print_string "exit 1";!Formatter.format#print_newline();
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
	!Formatter.format#print_string "exit 2";!Formatter.format#print_newline();
*)
	(r,([],[]))
      end
    else 
      if (if false then (compare p q = 0) else false) then 
	begin
(*
	  !Formatter.format#print_string "exit 3";!Formatter.format#print_newline();
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
			      !Formatter.format#print_string "exit 4";!Formatter.format#print_newline();
*)
			      ((bisim_empty bisim p q d [] []),([],[]))
			    end
		      end
		    else 
		      begin
(*
			!Formatter.format#print_string "exit 5";!Formatter.format#print_newline();
*)
			((bisim_empty bisim p q d [] []),([],[]))
		      end
		end
	  else 
	    begin
(*	      !Formatter.format#print_string "Incompatible arities.";!Formatter.format#print_newline(); *)
(*
	      !Formatter.format#print_string "exit 6";!Formatter.format#print_newline();
*)
	      ((bisim_empty bisim p q d [] []),([],[]))
	    end
and matches bisim env s_comm w_comm (* trace_p_strong trace_q_weak *) (* trace_p_weak trace_q_strong *) p_comm q_comm d  r =
  if Bisimulations.is_empty r then 
    begin
(*      !Formatter.format#print_string "Bisim empty.";!Formatter.format#print_newline(); *)
(*
      !Formatter.format#print_string "exit 7";!Formatter.format#print_newline();
*)
      (Bisimulations.empty,([],[]))
    end
  else
    if Commitments.is_empty p_comm then 
      begin
(*
	!Formatter.format#print_string "exit 8";!Formatter.format#print_newline();
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
  not_bisim := ExtBisimulations.empty

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
let next_commitments env p = 
  clear_all();
  commitments env 0 (concretise env p)
