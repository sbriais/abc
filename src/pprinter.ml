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
open Bisimulation
open Sprinter

let rec pp_list f g pp_a = function
    [] -> ()
  | [x] -> pp_a x;g()
  | x::xs -> pp_a x;f();pp_list f g pp_a xs

let pp_list_var lvl l =
  pp_list (function () -> !Formatter.format#print_string " ") (!Formatter.format#print_newline) (function n -> !Formatter.format#print_string (string_of_var lvl n)) l

let pp_list_string l =
  pp_list (function () -> !Formatter.format#print_string " ") (!Formatter.format#print_newline) (!Formatter.format#print_string) l

let rec pp_agent lvl = function
    Nil -> 
      !Formatter.format#open_box 0;
      !Formatter.format#print_string "0";
      !Formatter.format#close_box ()
  | Prefix(a,p) -> 
      !Formatter.format#open_box 2;
      !Formatter.format#print_string (string_of_action lvl a);
      (match a with
	   Input(_) -> pp_agent_prefix lvl I false p
	 | Output(_) -> pp_agent_prefix lvl O false p
	 | Tau -> !Formatter.format#print_string ".";!Formatter.format#print_space();pp_agent lvl p);
      !Formatter.format#close_box ()
  | Conc(n,p) ->
      !Formatter.format#open_box 2;
      !Formatter.format#print_string ("["^(string_of_var lvl n)^"]");
      !Formatter.format#print_space();
      pp_agent lvl p;
      !Formatter.format#close_box()
  | Abs(p) ->
      let rec aux lvl = function
	  Abs(q) -> 
	    !Formatter.format#print_string ",";
	    !Formatter.format#print_space();
	    !Formatter.format#print_string (string_of_var (lvl+1) Name.zero);
	    aux (lvl+1) q
	| q -> 
	    !Formatter.format#print_string ")";
	    !Formatter.format#print_space();
	    pp_agent lvl q
      in
	!Formatter.format#open_box 2;
	!Formatter.format#print_string "(\\";
	!Formatter.format#print_string (string_of_var (lvl+1) Name.zero);
	aux (lvl+1) p;
	!Formatter.format#close_box()
  | Nu(p) ->
      let rec aux lvl = function
	  Nu(q) -> 
	    !Formatter.format#print_string ",";
	    !Formatter.format#print_space();
	    !Formatter.format#print_string (string_of_var (lvl+1) Name.zero);
	    aux (lvl+1) q
	| q -> 
	    !Formatter.format#print_string ")";
	    !Formatter.format#print_space();
	    pp_agent lvl q
      in
	!Formatter.format#open_box 2;
	!Formatter.format#print_string "(^";
	!Formatter.format#print_string (string_of_var (lvl+1) Name.zero);
	aux (lvl+1) p;
	!Formatter.format#close_box()
  | Match(n,m,p) ->
      !Formatter.format#open_box 4;
      !Formatter.format#print_string ("["^(string_of_var lvl n)^"="^(string_of_var lvl m)^"]");
      !Formatter.format#print_space();
      pp_agent lvl p;
      !Formatter.format#close_box()
  | AgentRef(s) ->
      !Formatter.format#open_box 0;
      !Formatter.format#print_string s;
      !Formatter.format#close_box()
  | Apply(p,n) ->
      !Formatter.format#open_box 0;
      pp_agent lvl p;
      !Formatter.format#print_space();
      !Formatter.format#print_string (string_of_var lvl n);
      !Formatter.format#close_box()
  | Sum(ps) ->
      !Formatter.format#open_box 1;
      !Formatter.format#print_string "(";
      pp_list 
	(function () -> !Formatter.format#print_break 1 0;!Formatter.format#print_string "+";!Formatter.format#print_space()) 
	ignore
	(function p -> !Formatter.format#print_space ();!Formatter.format#print_if_newline();!Formatter.format#print_string " ";pp_agent lvl p) 
	(AgentMultiset.elements ps);
      !Formatter.format#print_space();
      !Formatter.format#print_string ")";
      !Formatter.format#close_box()
  | Parallel(ps) ->
      !Formatter.format#open_box 1;
      !Formatter.format#print_string "(";
      pp_list 
	(function () -> !Formatter.format#print_break 1 0;!Formatter.format#print_string "|";!Formatter.format#print_space()) 
	ignore
	(function p -> !Formatter.format#print_space ();!Formatter.format#print_if_newline();!Formatter.format#print_string " ";pp_agent lvl p) 
	(AgentMultiset.elements ps);      
      !Formatter.format#print_space();
      !Formatter.format#print_string ")";
      !Formatter.format#close_box()
and pp_agent_prefix lvl a b = function
    Abs(p) ->
      (match a with
	   I -> 
	     if b then
	       begin
		 !Formatter.format#print_string (", "^(string_of_var (lvl+1) Name.zero));
	       end
	     else
	       begin
		 !Formatter.format#open_box 0;
		 !Formatter.format#print_string ("("^(string_of_var (lvl+1) Name.zero))
	       end;
	     pp_agent_prefix (lvl+1) I true p
	 | O ->
	     if b then
	       begin
		 !Formatter.format#print_string ")";
		 !Formatter.format#close_box()
	       end;
	     !Formatter.format#print_string ".";!Formatter.format#print_space();
	     pp_agent lvl (Abs(p)))
  | Conc(n,p) ->
      (match a with
	   I -> 
	     if b then 
	       begin
		 !Formatter.format#print_string ">";
		 !Formatter.format#close_box()
	       end;
	     !Formatter.format#print_string ".";!Formatter.format#print_space();
	     pp_agent lvl (Conc(n,p))
	 | O -> 
	     if b then
	       begin
		 !Formatter.format#print_string (", "^(string_of_var lvl n));
	       end
	     else 
	       begin
		 !Formatter.format#open_box 0;
		 !Formatter.format#print_string ("<"^(string_of_var lvl n))
	       end;
	       pp_agent_prefix lvl O true p)
  | p ->
      (match a with
	   I -> 
	     if b then
	       begin
		 !Formatter.format#print_string ")";
		 !Formatter.format#close_box()
	       end
	 | O ->
	     if b then
	       begin
		 !Formatter.format#print_string ">";
		 !Formatter.format#close_box()
	       end);
      !Formatter.format#print_string ".";!Formatter.format#print_space();
      pp_agent lvl p 

let pp_agent_meta lvl p =
  !Formatter.format#open_box 0;
  !Formatter.format#print_string (string_of_agent lvl p);
  !Formatter.format#close_box ()

let pp_cond lvl c =
  let l = NameCond.elements c in
    !Formatter.format#open_box 0;
    !Formatter.format#print_string "{";!Formatter.format#print_space();
    pp_list 
      (function () -> !Formatter.format#print_string ",";!Formatter.format#print_space())
      ignore
      (function l -> !Formatter.format#open_box 0;pp_list (function () -> !Formatter.format#print_string "=") ignore (function x -> !Formatter.format#print_string (string_of_var lvl x)) l;!Formatter.format#close_box ()) l;
    !Formatter.format#print_space();!Formatter.format#print_string "}";
    !Formatter.format#close_box ()

let pp_comm org lvl (c,a,p) =
  !Formatter.format#open_box 0;
  pp_cond lvl c;
  !Formatter.format#print_space ();
  !Formatter.format#print_string " => ";
  !Formatter.format#print_space ();
  pp_agent_meta lvl org;
  !Formatter.format#print_space ();
  !Formatter.format#print_string ("--"^(string_of_action lvl a)^"->");
  !Formatter.format#print_space();
  pp_agent_meta lvl p;
  !Formatter.format#force_newline();
  !Formatter.format#close_box()

let pp_comms org lvl c =
  ignore (List.fold_left (fun n comm -> !Formatter.format#print_string ((string_of_int n)^": ");pp_comm org lvl comm;!Formatter.format#force_newline();n+1) 1 c);
  if (flush_entries pp_agent_meta) then !Formatter.format#force_newline()

let pp_dist lvl d =
  let l = NameDist.elements d in
    !Formatter.format#open_box 2;
    !Formatter.format#print_string "{";
    if l <> [] then 
      begin
	!Formatter.format#force_newline();
	List.iter 
	  (function (x,y) -> 
	     !Formatter.format#print_string ("("^(string_of_var lvl x)^", "^(string_of_var lvl y)^")");!Formatter.format#print_space ()) l;
	!Formatter.format#close_box ();
	!Formatter.format#force_newline();
	!Formatter.format#print_string "}"
      end
    else
      begin
	!Formatter.format#print_string " }";
	!Formatter.format#close_box()
      end

let pp_bisim lvl (p,q,d) =
  !Formatter.format#open_box 2;
  !Formatter.format#print_string "(";
  !Formatter.format#force_newline();
  pp_agent_meta lvl p;
  !Formatter.format#force_newline();
  pp_dist lvl d;
  !Formatter.format#force_newline();
  pp_agent_meta lvl q;
  !Formatter.format#close_box();
  !Formatter.format#force_newline();
  !Formatter.format#print_string ")"

let pp_bisims lvl bisim =
  !Formatter.format#open_box 2;
  !Formatter.format#print_string "{";
  !Formatter.format#force_newline();
  pp_list 
    (function () -> 
       !Formatter.format#force_newline();
       !Formatter.format#force_newline();
       if flush_entries pp_agent_meta then !Formatter.format#force_newline()) 
    (function () -> 
       if is_flushed () then 
	 begin
	   !Formatter.format#close_box();
	   !Formatter.format#force_newline()
	 end
       else
	 begin
	   !Formatter.format#force_newline();
	   !Formatter.format#force_newline();
	   ignore (flush_entries pp_agent_meta);
	   !Formatter.format#close_box();
	   !Formatter.format#force_newline()
	 end)
    (pp_bisim lvl) (Bisimulations.elements bisim);
  !Formatter.format#print_string "}";
  !Formatter.format#force_newline()


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

let pp_agent_latex lvl p = !Formatter.format#print_string (latex_of_agent lvl p)

let pp_traces tp tq wk =
  let string_of_transition = function
      Strong(alpha)  -> "-"^(string_of_action 0 alpha)^"->"
    | Weak(alpha) -> wk^(string_of_action 0 alpha)^wk^">" in
  let neg_transition = function
      Strong(alpha) -> Weak(alpha)
    | Weak(alpha) -> Strong(alpha) in
  let print_aux (op,oq) =
    !Formatter.format#print_newline();
    match op with
	Some(alpha,p) ->
	  !Formatter.format#print_string (string_of_transition alpha);!Formatter.format#print_newline();
	  (match oq with 
	       Some(beta,q) ->
		 !Formatter.format#print_string (string_of_transition beta);!Formatter.format#print_newline();
		 !Formatter.format#print_newline();
		 pp_agent_meta 0 p;!Formatter.format#print_newline();
		 pp_agent_meta 0 q;
	     | None ->
		 !Formatter.format#print_string (string_of_transition (neg_transition alpha));!Formatter.format#print_newline();
		 !Formatter.format#print_newline();
		 pp_agent_meta 0 p;!Formatter.format#print_newline();
		 !Formatter.format#print_string "*")
      | None ->
	  (match oq with 
	       Some(beta,q) ->
		 !Formatter.format#print_string (string_of_transition (neg_transition beta));!Formatter.format#print_newline();
		 !Formatter.format#print_string (string_of_transition beta);!Formatter.format#print_newline();
		 !Formatter.format#print_newline();
		 !Formatter.format#print_string "*";!Formatter.format#print_newline();
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
    pp_list !Formatter.format#print_newline !Formatter.format#print_newline print_aux trace


