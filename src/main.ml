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
open Commands

let env = new Agent.environment

let lexer lexbuf = new Parser.lexer Lexer.command lexbuf

let parse_command lexer = Parser.command lexer

let parse_yes_no lexer = Parser.yes_no lexer 

let parse_number lexer = Parser.number lexer

let lexer_stdin = lexer (Lexing.from_channel stdin)

let rec step_agent org comp_org comp_comm comms =
  match comms with
      [] -> 
	!Formatter.format#print_string "no more commitments";
	!Formatter.format#print_newline()
    | _ ->
	begin
	  Pprinter.pp_comms org 0 comms;
	  !Formatter.format#print_flush ();
	  let n = List.length comms in
	  let choix = ref (-1) in
	    while (!choix) = -1 do
	      !Formatter.format#print_string ("Please choose a commitment (between 1 and "^(string_of_int n)^") or 0 to exit: ");
	      !Formatter.format#print_flush ();
	      (try
		 choix := parse_number lexer_stdin;
		 if ((!choix) > n) || ((!choix) < 0) then 
		   begin
		     choix := -1;
		     !Formatter.format#print_string "Invalid commitment.";
		     !Formatter.format#print_newline()
		   end
	       with
		   Failure(s) ->  
		     begin
		       !Formatter.format#print_string s;
		       !Formatter.format#print_newline();
		     end
	       );
	    done;
	    if (!choix) > 0 then
	      let (c,a,p) = List.nth comms ((!choix)-1) in
		step_agent (comp_org p) comp_org comp_comm (Agent.Commitments.elements (comp_comm (c,a,p)))
	    else ()
	end

let see_bisim flag bisim =
  let choix = ref None in
    while (!choix) = None do
      !Formatter.format#print_string ("Do you want to see the core of the "^(if flag then "bi" else "")^"simulation (yes/no) ? ");
      !Formatter.format#print_flush (); 
      (try
	 choix := Some(parse_yes_no lexer_stdin)
       with
	   Failure(s) ->
	     begin
	       !Formatter.format#print_string s;
	       !Formatter.format#print_newline();
	     end)
    done;
    match (!choix) with
	Some(true) -> Pprinter.pp_bisims 0 bisim
      | _ -> ()


let see_trace a b ta tb wk =
  let choix = ref None in
    while (!choix) = None do
      !Formatter.format#print_string "Do you want to see some traces (yes/no) ? ";
      !Formatter.format#print_flush (); 
      (try
	 choix := Some(parse_yes_no lexer_stdin)
       with
	   Failure(s) ->
	     begin
	       !Formatter.format#print_string s;
	       !Formatter.format#print_newline();
	     end)
    done;
    match (!choix) with
	Some(true) ->
	    begin
	      let show_traces p q tp tq =
		!Formatter.format#print_string "traces of ";
		!Formatter.format#print_newline ();
		!Formatter.format#print_newline ();
		!Formatter.format#open_box 0;
		Pprinter.pp_agent 0 p;
		!Formatter.format#close_box();
		!Formatter.format#print_newline ();
		!Formatter.format#open_box 0;
		Pprinter.pp_agent 0 q;
		!Formatter.format#close_box();
		!Formatter.format#print_newline ();
		Pprinter.pp_traces tp tq wk;
		!Formatter.format#print_newline();
		if (Pprinter.flush_entries Pprinter.pp_agent_meta) then !Formatter.format#force_newline()
	      in
		show_traces a b ta tb
	    end
      | _ -> ()
		

let rec handle_command = function
    Def(s,a) -> 
      begin
	let fn = Agent.free_names env a in
	  if Agent.NameSet.is_empty fn then
	    begin
	      env#add_agent s a;
	      !Formatter.format#print_string ("Agent "^s^" is defined.");
	      !Formatter.format#print_newline()
	    end
	  else
	    begin
	      !Formatter.format#print_string ("Agent "^s^" is not defined because there are free variables:");
	      Agent.NameSet.iter (function n -> !Formatter.format#print_string (" "^(Pprinter.string_of_var 0 n))) fn;
	      !Formatter.format#print_newline()
	    end
      end
  | Exit -> exit 0
  | Eqd(l,a,b) ->
      begin
	let fn = Agent.NameSet.union (Agent.free_names env a) (Agent.free_names env b) in
	let l = Agent.NameSet.elements (Agent.NameSet.inter (Agent.set_of_list l) fn) in
	let d = Agent.dist_of_lists l (Agent.NameSet.elements fn) in
	let (n,bisim,(ta,tb)) = Agent.eq env a b d in
	  (match n with
	       0 -> 
		 !Formatter.format#print_string ("The two agents are not strongly related ("^(string_of_int (List.length ta))^").");
		 !Formatter.format#print_newline();
		 see_trace a b ta tb "-"
	     | n -> 
		 !Formatter.format#print_string ("The two agents are strongly related ("^(string_of_int n)^").");
		 !Formatter.format#print_newline();
		 see_bisim true bisim
	  );
      end
  | Weqd(l,a,b) ->
      begin
	let fn = Agent.NameSet.union (Agent.free_names env a) (Agent.free_names env b) in
	let l = Agent.NameSet.elements (Agent.NameSet.inter (Agent.set_of_list l) fn) in
	let d = Agent.dist_of_lists l (Agent.NameSet.elements fn) in
	let (n,bisim,(ta,tb)) = Agent.weq env a b d in
	  (match n with
	       0 -> 
		 !Formatter.format#print_string ("The two agents are not weakly related ("^(string_of_int (List.length ta))^").");
		 !Formatter.format#print_newline();
		 see_trace a b ta tb "="
	     | n -> 
		 !Formatter.format#print_string ("The two agents are weakly related ("^(string_of_int n)^").");
		 !Formatter.format#print_newline();
		 see_bisim true bisim
	  );
      end
  | Ltd(l,a,b) ->
      begin
	let fn = Agent.NameSet.union (Agent.free_names env a) (Agent.free_names env b) in
	let l = Agent.NameSet.elements (Agent.NameSet.inter (Agent.set_of_list l) fn) in
	let d = Agent.dist_of_lists l (Agent.NameSet.elements fn) in
	let (n,bisim,(ta,tb)) = Agent.lt env a b d in
	  (match n with
	       0 -> 
		 !Formatter.format#print_string ("The two agents are not strongly related ("^(string_of_int (List.length ta))^").");
		 !Formatter.format#print_newline();
		 see_trace a b ta tb "-"
	     | n -> 
		 !Formatter.format#print_string ("The two agents are strongly related ("^(string_of_int n)^").");
		 !Formatter.format#print_newline();
		 see_bisim false bisim
	  );
      end
  | Wltd(l,a,b) ->
      begin
	let fn = Agent.NameSet.union (Agent.free_names env a) (Agent.free_names env b) in
	let l = Agent.NameSet.elements (Agent.NameSet.inter (Agent.set_of_list l) fn) in
	let d = Agent.dist_of_lists l (Agent.NameSet.elements fn) in
	let (n,bisim,(ta,tb)) = Agent.wlt env a b d in
	  (match n with
	       0 -> 
		 !Formatter.format#print_string ("The two agents are not weakly related ("^(string_of_int (List.length ta))^").");
		 !Formatter.format#print_newline();
		 see_trace a b ta tb "="
	     | n -> 
		 !Formatter.format#print_string ("The two agents are weakly related ("^(string_of_int n)^").");
		 !Formatter.format#print_newline();
		 see_bisim false bisim
	  );
      end
  | Show(a) -> 
      begin
	!Formatter.format#open_box 0;
	Pprinter.pp_agent 0 (Agent.standard_form env 0 a);
	!Formatter.format#close_box();
	!Formatter.format#print_newline()
      end
  | Print(a) ->
      begin
	!Formatter.format#open_box 0;
	Pprinter.pp_agent 0 a;
	!Formatter.format#close_box();
	!Formatter.format#print_newline()
      end
  | Latex(a) ->
      begin
	!Formatter.format#open_box 0;
	Pprinter.pp_agent_latex 0 a;
	!Formatter.format#close_box();
	!Formatter.format#print_newline()
      end
  | Reset ->
      begin
	Agent_parse.helper#reset;
	env#reset;
	!Formatter.format#print_string "Reinitialised.";
	!Formatter.format#print_newline()
      end
  | Clear(ids) ->
      begin
	!Formatter.format#print_string "Clearing ";
	Pprinter.pp_list_string ids;
	List.iter (function id -> Agent_parse.helper#clear id) ids;
      end
  | Load(f) ->
      begin
	let read_file f =
	  let rec batch lexer =
	    (try
	       let com = parse_command lexer in
		 handle_command com;
		 batch lexer
	     with
		 Failure(s) -> 
		   begin
		     !Formatter.format#print_string s;
		     !Formatter.format#print_newline();
		     batch lexer
		   end
	       | Parsing.Parse_error ->
		   begin
		     !Formatter.format#print_newline();
		     !Formatter.format#print_string "Parse error";
		     !Formatter.format#print_newline();
		     !Formatter.format#print_string "Aborting...";
		     !Formatter.format#print_newline();
		   end
	       | Lexer.Eof
	       | End_of_file -> () (* !Formatter.format#print_string "End of file";!Formatter.format#print_newline() *)
	       | Not_found ->
		   begin
		     !Formatter.format#print_string "Something is not defined.";
		     !Formatter.format#print_newline();
		     batch lexer
		   end
	       | Agent.Not_defined(s) ->
		   begin
		     !Formatter.format#print_string ("Agent "^s^" is not defined.");
		     !Formatter.format#print_newline();
		     batch lexer
		   end
	       | e -> 
		   begin
		     !Formatter.format#print_string "Oops... unexpected error";
		     !Formatter.format#print_newline();
		     raise e;
		     batch lexer
		   end)
	  in
	  let in_descr=Unix.openfile f [Unix.O_RDONLY] 0 in	  
	  let in_channel=Unix.in_channel_of_descr in_descr in
	    batch (lexer (Lexing.from_channel in_channel));
	    Unix.close in_descr
	in
	  !Formatter.format#print_string ("Opening file "^f);!Formatter.format#print_newline();
	  (try
	     read_file f;
	     !Formatter.format#print_string ("Closing file "^f);!Formatter.format#print_newline();
	   with
	       Unix.Unix_error(_) -> 
		 !Formatter.format#print_string ("Error while opening file...");!Formatter.format#print_newline ())
      end
  | Step(a) ->
      begin
	step_agent
	  a
	  (Agent.concretise env)
	  (fun (_,_,p) -> Agent.next_commitments env p) 
	  (Agent.Commitments.elements (Agent.next_commitments env (Agent.standard_form env 0 a)))
      end
  | Push(l) ->
      begin
	!Formatter.format#print_string "Pushing ";
	Pprinter.pp_list_var 0 l;
	List.iter (function x -> Agent_parse.helper#push x) l;
      end
  | Pop(n) ->
      begin

	let l = Agent_parse.helper#pop n in
	  match l with 
	      [] -> 
		!Formatter.format#print_string "Nothing to pop!";!Formatter.format#print_newline()
	    | _ -> 
		!Formatter.format#print_string "Popping ";Pprinter.pp_list_var 0 l
      end;
  | Implicit ->
      begin
	match (Agent_parse.helper#get_current_context) with
	    [] -> 
	      !Formatter.format#print_string "No implicit variables.";
	      !Formatter.format#print_newline()
	  | l -> 
	      !Formatter.format#print_string "Implicit variables are ";
	      Pprinter.pp_list_var 0 l
      end
  | Nocommand -> ()
  | Help ->
      begin
	!Formatter.format#print_string ("ABC v. "^(Compile_info.version));!Formatter.format#print_newline ();
	!Formatter.format#print_string (Compile_info.build_info);!Formatter.format#print_newline ();
	!Formatter.format#print_string (Compile_info.date_of_compile);!Formatter.format#print_newline ();
	!Formatter.format#print_string "---";!Formatter.format#print_newline ();
	!Formatter.format#print_string "agent <Name[(params)]> = <agent>";!Formatter.format#print_newline();
	!Formatter.format#print_string "   define the agent <Name(params)> with the body <agent>";!Formatter.format#print_newline();
	!Formatter.format#print_string "eq <agent1> <agent2>";!Formatter.format#print_newline();
	!Formatter.format#print_string "   check strong equivalence between <agent1> and <agent2>";!Formatter.format#print_newline();
	!Formatter.format#print_string "eqd <(v1,...,vn)> <agent1> <agent2>";!Formatter.format#print_newline();
	!Formatter.format#print_string "   check strong equivalence between <agent1> and <agent2> with distinction pwd(v1,...,vn,fn agent1,fn agent2)";!Formatter.format#print_newline();
	!Formatter.format#print_string "weq <agent1> <agent2>";!Formatter.format#print_newline();
	!Formatter.format#print_string "   check weak equivalence between <agent1> and <agent2>";!Formatter.format#print_newline();
	!Formatter.format#print_string "weqd <(v1,...,vn)> <agent1> <agent2>";!Formatter.format#print_newline();
	!Formatter.format#print_string "   check weak equivalence between <agent1> and <agent2> with distinction pwd(v1,...,vn,fn agent1,fn agent2)";!Formatter.format#print_newline();
	!Formatter.format#print_string "show <agent>";!Formatter.format#print_newline();
	!Formatter.format#print_string "   show standard form of <agent>";!Formatter.format#print_newline();
	!Formatter.format#print_string "print <agent>";!Formatter.format#print_newline();
	!Formatter.format#print_string "   (pretty-)print <agent>";!Formatter.format#print_newline();
	!Formatter.format#print_string "latex <agent>";!Formatter.format#print_newline();
	!Formatter.format#print_string "   generate LaTeX code for <agent> (use some LaTeX macros)";!Formatter.format#print_newline();
	!Formatter.format#print_string "step <agent>";!Formatter.format#print_newline();
	!Formatter.format#print_string "   interactive exploration of the commitments of <agent>";!Formatter.format#print_newline();
	!Formatter.format#print_string "reset";!Formatter.format#print_newline();
	!Formatter.format#print_string "   reinitialise the workbench";!Formatter.format#print_newline();
	!Formatter.format#print_string "exit";!Formatter.format#print_newline();
	!Formatter.format#print_string "   exit the workbench";!Formatter.format#print_newline();
	!Formatter.format#print_string "help";!Formatter.format#print_newline();
	!Formatter.format#print_string "   this help";!Formatter.format#print_newline();
	!Formatter.format#print_string "   further information can be found in the ABC user guide";!Formatter.format#print_newline();
      end
  | Rate(n) ->
      if (0 <= n) && (n <= !Agent.max_rate) then
	begin
	  Agent.buffer_switch n;
	  !Formatter.format#print_string ("Caching rate is now "^(string_of_int !Agent.buffer_rate)^"/"^(string_of_int (!Agent.max_rate))^".");
	end
      else
	!Formatter.format#print_string "Invalid rate.";
      !Formatter.format#print_newline();
  | Maxrate(n) ->
      if n > 0 then
	begin
	  Agent.set_maxrate n;
	  !Formatter.format#print_string ("Caching rate is now "^(string_of_int !Agent.buffer_rate)^"/"^(string_of_int (!Agent.max_rate))^".");
	end
      else
	!Formatter.format#print_string "Invalid bound.";
      !Formatter.format#print_newline()
  | List(l) ->
      match l with
	  [] -> ()
	| x::xs -> (handle_command x;handle_command (List(xs)))
  | _ ->
      begin
	!Formatter.format#print_string "Not yet implemented.";
	!Formatter.format#print_newline();
      end

let welcome () = 
  !Formatter.format#print_string "Welcome to Another Bisimulation Checker";
  !Formatter.format#print_newline()

let _ =
  welcome ();
  let rec loop () = 
    (try
       !Formatter.format#print_string "abc > ";!Formatter.format#print_flush ();
       let com = parse_command lexer_stdin in
	 handle_command com;
	 loop ()
     with
	 Failure(s) -> 
	   begin
	     !Formatter.format#print_string s;
	     !Formatter.format#print_newline();
	     loop ()
	   end
       | Parsing.Parse_error ->
	   begin
	     !Formatter.format#print_newline();
	     !Formatter.format#print_string "Parse error";
	     !Formatter.format#print_newline();
	     loop ()
	   end
       | Lexer.Eof
       | End_of_file ->
	   begin
	     !Formatter.format#print_newline();
	     !Formatter.format#print_string "Bye bye !";
	     !Formatter.format#print_newline();
	     exit 0
	   end
       | Not_found ->
	   begin
	     !Formatter.format#print_string "Something is not defined.";
	     !Formatter.format#print_newline();
	     loop ()
	   end
       | Agent.Not_defined(s) ->
	   begin
	     !Formatter.format#print_string ("Agent "^s^" is not defined.");
	     !Formatter.format#print_newline();
	     loop ()
	   end
       | e -> 
	   begin
	     !Formatter.format#print_string "Oops... unexpected error";
	     !Formatter.format#print_newline();
	     raise e;
	     loop ()
	   end)
  in
    loop ()

