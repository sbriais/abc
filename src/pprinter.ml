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

let rec pp_list f g pp_a = function
    [] -> ()
  | [x] -> pp_a x;g()
  | x::xs -> pp_a x;f();pp_list f g pp_a xs

let pp_list_var lvl l =
  pp_list (function () -> Format.print_string " ") (Format.print_newline) (function n -> Format.print_string (string_of_var lvl n)) l

let pp_list_string l =
  pp_list (function () -> Format.print_string " ") (Format.print_newline) (Format.print_string) l

type pp_action = I | O

let rec pp_agent lvl = function
    Nil -> 
      Format.open_box 0;
      Format.print_string "0";
      Format.close_box ()
  | Prefix(a,p) -> 
      Format.open_box 2;
      Format.print_string (string_of_action lvl a);
      (match a with
	   Input(_) -> pp_agent_prefix lvl I false p
	 | Output(_) -> pp_agent_prefix lvl O false p
	 | Tau -> Format.print_string ".";Format.print_space();pp_agent lvl p);
      Format.close_box ()
  | Conc(n,p) ->
      Format.open_box 2;
      Format.print_string ("["^(string_of_var lvl n)^"]");
      Format.print_space();
      pp_agent lvl p;
      Format.close_box()
  | Abs(p) ->
      let rec aux lvl = function
	  Abs(q) -> 
	    Format.print_string ",";
	    Format.print_space();
	    Format.print_string (string_of_var (lvl+1) Name.zero);
	    aux (lvl+1) q
	| q -> 
	    Format.print_string ")";
	    Format.print_space();
	    pp_agent lvl q
      in
	Format.open_box 2;
	Format.print_string "(\\";
	Format.print_string (string_of_var (lvl+1) Name.zero);
	aux (lvl+1) p;
	Format.close_box()
  | Nu(p) ->
      let rec aux lvl = function
	  Nu(q) -> 
	    Format.print_string ",";
	    Format.print_space();
	    Format.print_string (string_of_var (lvl+1) Name.zero);
	    aux (lvl+1) q
	| q -> 
	    Format.print_string ")";
	    Format.print_space();
	    pp_agent lvl q
      in
	Format.open_box 2;
	Format.print_string "(^";
	Format.print_string (string_of_var (lvl+1) Name.zero);
	aux (lvl+1) p;
	Format.close_box()
  | Match(n,m,p) ->
      Format.open_box 4;
      Format.print_string ("["^(string_of_var lvl n)^"="^(string_of_var lvl m)^"]");
      Format.print_space();
      pp_agent lvl p;
      Format.close_box()
  | AgentRef(s) ->
      Format.open_box 0;
      Format.print_string s;
      Format.close_box()
  | Apply(p,n) ->
      Format.open_box 0;
      pp_agent lvl p;
      Format.print_space();
      Format.print_string (string_of_var lvl n);
      Format.close_box()
  | Sum(ps) ->
      Format.open_box 1;
      Format.print_string "(";
      pp_list 
	(function () -> Format.print_break 1 0;Format.print_string "+";Format.print_space()) 
	ignore
	(function p -> Format.print_space ();Format.print_if_newline();Format.print_string " ";pp_agent lvl p) 
	(AgentMultiset.elements ps);
      Format.print_space();
      Format.print_string ")";
      Format.close_box()
  | Parallel(ps) ->
      Format.open_box 1;
      Format.print_string "(";
      pp_list 
	(function () -> Format.print_break 1 0;Format.print_string "|";Format.print_space()) 
	ignore
	(function p -> Format.print_space ();Format.print_if_newline();Format.print_string " ";pp_agent lvl p) 
	(AgentMultiset.elements ps);      
      Format.print_space();
      Format.print_string ")";
      Format.close_box()
and pp_agent_prefix lvl a b = function
    Abs(p) ->
      (match a with
	   I -> 
	     if b then
	       begin
		 Format.print_string (", "^(string_of_var (lvl+1) Name.zero));
	       end
	     else
	       begin
		 Format.open_box 0;
		 Format.print_string ("("^(string_of_var (lvl+1) Name.zero))
	       end;
	     pp_agent_prefix (lvl+1) I true p
	 | O ->
	     if b then
	       begin
		 Format.print_string ")";
		 Format.close_box()
	       end;
	     Format.print_string ".";Format.print_space();
	     pp_agent lvl (Abs(p)))
  | Conc(n,p) ->
      (match a with
	   I -> 
	     if b then 
	       begin
		 Format.print_string ">";
		 Format.close_box()
	       end;
	     Format.print_string ".";Format.print_space();
	     pp_agent lvl (Conc(n,p))
	 | O -> 
	     if b then
	       begin
		 Format.print_string (", "^(string_of_var lvl n));
	       end
	     else 
	       begin
		 Format.open_box 0;
		 Format.print_string ("<"^(string_of_var lvl n))
	       end;
	       pp_agent_prefix lvl O true p)
  | p ->
      (match a with
	   I -> 
	     if b then
	       begin
		 Format.print_string ")";
		 Format.close_box()
	       end
	 | O ->
	     if b then
	       begin
		 Format.print_string ">";
		 Format.close_box()
	       end);
      Format.print_string ".";Format.print_space();
      pp_agent lvl p 

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
	       Format.print_string ("#"^(string_of_int head)^" ::= ");
	       (*Format.print_space();*)
	       pp_agent lvl p;
	       Format.force_newline());
	flush_entries pp_agent
  in
  let flush_entries pp_agent =
    Format.open_box 0;
    let b = (if is_flushed () then false
	     else
	       begin
		 flush_entries pp_agent;
		 true
	       end) in
      Format.close_box();b
  in
    (get_entry,reset_entries,flush_entries,is_flushed)

let trunk_size = 10

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
      
	   
let pp_agent_meta lvl p =
  Format.open_box 0;
  Format.print_string (string_of_agent lvl p);
  Format.close_box ()

let pp_cond lvl c =
  let l = NameCond.elements c in
    Format.open_box 0;
    Format.print_string "{";Format.print_space();
    pp_list 
      (function () -> Format.print_string ",";Format.print_space())
      ignore
      (function l -> Format.open_box 0;pp_list (function () -> Format.print_string "=") ignore (function x -> Format.print_string (string_of_var lvl x)) l;Format.close_box ()) l;
    Format.print_space();Format.print_string "}";
    Format.close_box ()

let pp_comm org lvl (c,a,p) =
  Format.open_box 0;
  pp_cond lvl c;
  Format.print_space ();
  Format.print_string " => ";
  Format.print_space ();
  pp_agent_meta lvl org;
  Format.print_space ();
  Format.print_string ("--"^(string_of_action lvl a)^"->");
  Format.print_space();
  pp_agent_meta lvl p;
  Format.force_newline();
  Format.close_box()

let pp_comms org lvl c =
  ignore (List.fold_left (fun n comm -> Format.print_string ((string_of_int n)^": ");pp_comm org lvl comm;Format.force_newline();n+1) 1 c);
  if (flush_entries pp_agent_meta) then Format.force_newline()

let pp_dist lvl d =
  let l = NameDist.elements d in
    Format.open_box 2;
    Format.print_string "{";
    if l <> [] then 
      begin
	Format.force_newline();
	List.iter 
	  (function (x,y) -> 
	     Format.print_string ("("^(string_of_var lvl x)^", "^(string_of_var lvl y)^")");Format.print_space ()) l;
	Format.close_box ();
	Format.force_newline();
	Format.print_string "}"
      end
    else
      begin
	Format.print_string " }";
	Format.close_box()
      end

let pp_bisim lvl (p,q,d) =
  Format.open_box 2;
  Format.print_string "(";
  Format.force_newline();
  pp_agent_meta lvl p;
  Format.force_newline();
  pp_dist lvl d;
  Format.force_newline();
  pp_agent_meta lvl q;
  Format.close_box();
  Format.force_newline();
  Format.print_string ")"

let pp_bisims lvl bisim =
  Format.open_box 2;
  Format.print_string "{";
  Format.force_newline();
  pp_list 
    (function () -> 
       Format.force_newline();
       Format.force_newline();
       if flush_entries pp_agent_meta then Format.force_newline()) 
    (function () -> 
       if is_flushed () then 
	 begin
	   Format.close_box();
	   Format.force_newline()
	 end
       else
	 begin
	   Format.force_newline();
	   Format.force_newline();
	   ignore (flush_entries pp_agent_meta);
	   Format.close_box();
	   Format.force_newline()
	 end)
    (pp_bisim lvl) (Bisimulations.elements bisim);
  Format.print_string "}";
  Format.force_newline()


let latex_of_action lvl = function
    Tau -> "\\tau"
  | Input(n) -> string_of_var lvl n
  | Output(n) -> "\\overline{"^(string_of_var lvl n)^"}"

let rec latex_of_agent lvl = function
    Nil -> "\\mathbf{0}"
  | Prefix(a,p) -> 
      (latex_of_action lvl a)^
      (match a with
	   Input(_) -> (latex_of_agent_prefix lvl I false p)
	 | Output(_) -> (latex_of_agent_prefix lvl O false p)
	 | Tau -> "."^(latex_of_agent lvl p))
  | Conc(n,p) ->
      "\\lbrack "^(string_of_var lvl n)^" \\rbrack "^(latex_of_agent lvl p)
  | Abs(p) ->
      let rec aux lvl = function
	  Abs(q) -> ", "^(string_of_var (lvl+1) Name.zero)^(aux (lvl+1) q)
	| q -> " \\right) "^(latex_of_agent lvl q)
      in
	"\\left( \\lambda "^(string_of_var (lvl+1) Name.zero)^(aux (lvl+1) p)
  | Nu(p) ->
      let rec aux lvl = function
	  Nu(q) -> ", "^(string_of_var (lvl+1) Name.zero)^(aux (lvl+1) q)
	| q -> " \\right) "^(latex_of_agent lvl q)
      in
	"\\left( \\nu "^(string_of_var (lvl+1) Name.zero)^(aux (lvl+1) p)
  | Match(n,m,p) ->
      "\\lbrack "^(string_of_var lvl n)^" = "^(string_of_var lvl m)^" \\rbrack "^(latex_of_agent lvl p)
  | AgentRef(s) ->
      "\\mathrm{"^s^"}"
  | Apply(p,n) ->
      "\\left( "^(latex_of_agent lvl p)^" \\right) "^(string_of_var lvl n)
  | Sum(ps) -> 
      (match (AgentMultiset.elements ps) with
	   [] -> ""
	 | [x] -> latex_of_agent lvl x
	 | (x::xs) as xss -> 
(*	     let operands = List.map (latex_of_agent lvl) xss in *)
	     "\\begin{array}{rl}\n & "^(List.fold_left (fun s x -> s^"+ & "^(latex_of_agent lvl x)^"\\\\\n") ((latex_of_agent lvl x)^"\\\\\n") xs)^"\\end{array}\n")
  | Parallel(ps) -> 
      (match (AgentMultiset.elements ps) with
	   [] -> ""
	 | [x] -> latex_of_agent lvl x
	 | x::xs -> "\\begin{array}{rl}\n & "^(List.fold_left (fun s x -> s^"| & "^(latex_of_agent lvl x)^"\\\\\n") ((latex_of_agent lvl x)^"\\\\\n") xs)^"\\end{array}\n")
and latex_of_agent_prefix lvl a b = function
    Abs(p) ->
      (match a with
	   I -> 
	     if b then
	       begin
		 ", "^(string_of_var (lvl+1) Name.zero)^(latex_of_agent_prefix (lvl+1) I true p)
	       end
	     else
	       begin
		 " \\left( "^(string_of_var (lvl+1) Name.zero)^(latex_of_agent_prefix (lvl+1) I true p)
	       end;
	 | O -> (if b then " \\right) " else "")^"."^(latex_of_agent lvl (Abs(p))))
  | Conc(n,p) ->
      (match a with
	   I -> (if b then " \\rangle " else "")^"."^(latex_of_agent lvl (Conc(n,p)))
	 | O -> 
	     if b then
	       begin
		 ", "^(string_of_var lvl n)^(latex_of_agent_prefix lvl O true p)
	       end
	     else 
	       begin
		 " \\langle "^(string_of_var lvl n)^(latex_of_agent_prefix lvl O true p)
	       end)
  | p -> (if b then 
	    match a with 
		I -> " \\right) "
	      | O -> " \\rangle "
	  else "")^"."^(latex_of_agent lvl p)

let pp_agent_latex lvl p = Format.print_string (latex_of_agent lvl p)

let pp_traces tp tq wk =
  let string_of_transition = function
      Strong(alpha)  -> "-"^(string_of_action 0 alpha)^"->"
    | Weak(alpha) -> wk^(string_of_action 0 alpha)^wk^">" in
  let neg_transition = function
      Strong(alpha) -> Weak(alpha)
    | Weak(alpha) -> Strong(alpha) in
  let print_aux (op,oq) =
    Format.print_newline();
    match op with
	Some(alpha,p) ->
	  Format.print_string (string_of_transition alpha);Format.print_newline();
	  (match oq with 
	       Some(beta,q) ->
		 Format.print_string (string_of_transition beta);Format.print_newline();
		 Format.print_newline();
		 pp_agent_meta 0 p;Format.print_newline();
		 pp_agent_meta 0 q;
	     | None ->
		 Format.print_string (string_of_transition (neg_transition alpha));Format.print_newline();
		 Format.print_newline();
		 pp_agent_meta 0 p;Format.print_newline();
		 Format.print_string "*")
      | None ->
	  (match oq with 
	       Some(beta,q) ->
		 Format.print_string (string_of_transition (neg_transition beta));Format.print_newline();
		 Format.print_string (string_of_transition beta);Format.print_newline();
		 Format.print_newline();
		 Format.print_string "*";Format.print_newline();
		 pp_agent_meta 0 q;
	     | None -> failwith "pp_traces")
  in
  let rec combine_rev accu = function
      [],[] -> accu
    | x::xs,y::ys ->
	combine_rev ((x,y)::accu) (xs,ys)
    | _ -> failwith "pp_traces: combine_rev"
  in
  let trace = List.rev (combine_rev [] (tp,tq)) in
    pp_list Format.print_newline Format.print_newline print_aux trace


