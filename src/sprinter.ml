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

type pp_action = I | O

let trunk_size = 10

(* quelques fonctions d'impression *)
let string_of_var lvl n = 
  if Name.is_free lvl n then
    begin
      let n' = Name.freename lvl n in
	match (Agent_parse.helper#reverse n') with
	    Some(s) -> s
	  | _ -> Name.to_string lvl n
    end
  else Name.to_string lvl n

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
  
let string_of_agent_simple = string_of_agent

let rec string_of_list f g = function
    [] -> ""
  | [x] -> (f x)
  | x::xs -> (f x)^(g ())^(string_of_list f g xs)

(* l should be NameCond.elements c *)
let string_of_cond lvl l = 
  "{"^(string_of_list (string_of_list (string_of_var lvl) (function () -> "=")) (function () -> ",") l)^"}"

(* l should be NameDist.elements d *)
let string_of_dist lvl l = 
  "{"^(string_of_list (function (x,y) -> "("^(string_of_var lvl x)^","^(string_of_var lvl y)^")") (function () -> "") l)^"}"

exception DFound of (int*Agent.agent)

let (get_entry,reset_entries,flush_entries,is_flushed) =
  let counter = ref 0 in
  let dico = ref AgentMap.empty in
  let to_flush = Queue.create () in
  let get_entry k =
    "#"^(string_of_int (try
			  AgentMap.find k (!dico)
			with
			    Not_found -> 
			      incr counter;
			      dico := AgentMap.add k (!counter) (!dico);
			      Queue.add (!counter) to_flush;
			      !counter))
  and reset_entries () =
    counter := 0;
    dico := AgentMap.empty;
    Queue.clear to_flush
  in
  let is_flushed () = Queue.length to_flush = 0 in
  let rec flush_entries (pp_agent:int->Agent.agent->unit) =
    if is_flushed () then ()
    else
      let head = Queue.take to_flush in
	(try
	   AgentMap.iter (fun k i -> if i = head then raise (DFound k) else ()) (!dico)
	 with
	     DFound(lvl,p) ->
	       !Formatter.format#print_string ("#"^(string_of_int head)^" ::= ");
	       (*!Formatter.format#print_space();*)
	       pp_agent lvl p;
	       !Formatter.format#force_newline());
	flush_entries pp_agent
  in
  let flush_entries pp_agent =
    !Formatter.format#open_box 0;
    let b = (if is_flushed () then false
	     else
	       begin
		 flush_entries pp_agent;
		 true
	       end) in
      !Formatter.format#close_box();b
  in
    (get_entry,reset_entries,flush_entries,is_flushed)

let rec string_of_agent lvl = function
    Nil -> "0"
  | Prefix(a,p) -> 
      (string_of_action lvl a)^
      (let s = 
	 (match a with
	      Tau -> "."^(string_of_agent lvl p)
	    | Input(_) -> string_of_agent_prefix lvl I false p
	    | Output(_) -> string_of_agent_prefix lvl O false p)
       in 
	 if String.length s < trunk_size then s 
	 else "."^(get_entry (lvl,p)))
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
and string_of_agent_prefix lvl a b = function
    Abs(p) ->
      (match a with
	   I -> 
	     (if b then ","^(string_of_var (lvl+1) (Name.zero))
	      else "("^(string_of_var (lvl+1) (Name.zero)))^(string_of_agent_prefix (lvl+1) a true p)
	 | O -> (if b then ")" else "")^"."^(string_of_agent lvl (Abs(p))))
  | Conc(n,p) ->
      (match a with
	   I -> (if b then ">" else "")^"."^(string_of_agent lvl (Conc(n,p)))
	 | O ->
	     (if b then ","^(string_of_var lvl n)
	      else "<"^(string_of_var lvl n))^(string_of_agent_prefix lvl a true p))
  | p ->
      (match a with
	   I -> if b then ")" else ""
	 | O -> if b then ">" else "")^"."^(string_of_agent lvl p)
