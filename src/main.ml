open Commands
open Pprinter

let env = new Agent.environment

let lexer lexbuf = new Parser.lexer Lexer.command lexbuf

let parse_command lexer = Parser.command lexer

let parse_yes_no lexer = Parser.yes_no lexer 

let parse_number lexer = Parser.number lexer

let lexer_stdin = lexer (Lexing.from_channel stdin)

let rec step_agent org comp_org comp_comm comms =
  match comms with
      [] -> 
	Format.print_string "no more commitments";
	Format.print_newline()
    | _ ->
	begin
	  pp_comms org 0 comms;
	  Format.print_flush ();
	  let n = List.length comms in
	  let choix = ref (-1) in
	    while (!choix) = -1 do
	      Format.print_string ("Please choose a commitment (between 1 and "^(string_of_int n)^") or 0 to exit: ");
	      Format.print_flush ();
	      (try
		 choix := parse_number lexer_stdin;
		 if ((!choix) > n) || ((!choix) < 0) then 
		   begin
		     choix := -1;
		     Format.print_string "Invalid commitment.";
		     Format.print_newline()
		   end
	       with
		   Failure(s) ->  
		     begin
		       Format.print_string s;
		       Format.print_newline();
		     end
	       );
	    done;
	    if (!choix) > 0 then
	      let (c,a,p) = List.nth comms ((!choix)-1) in
		step_agent (comp_org p) comp_org comp_comm (Agent.Commitments.elements (comp_comm (c,a,p)))
	    else ()
	end

let see_bisim bisim =
  let choix = ref None in
    while (!choix) = None do
      Format.print_string "Do you want to see the core of the bisimulation (yes/no) ? ";
      Format.print_flush (); 
      (try
	 choix := Some(parse_yes_no lexer_stdin)
       with
	   Failure(s) ->
	     begin
	       Format.print_string s;
	       Format.print_newline();
	     end)
    done;
    match (!choix) with
	Some(true) -> pp_bisims 0 bisim
      | _ -> ()


let see_trace a b =
  let choix = ref None in
    while (!choix) = None do
      Format.print_string "Do you want to see a trace that leads to distinguish the two processes (yes/no) ? ";
      Format.print_flush (); 
      (try
	 choix := Some(parse_yes_no lexer_stdin)
       with
	   Failure(s) ->
	     begin
	       Format.print_string s;
	       Format.print_newline();
	     end)
    done;
    match (!choix) with
	Some(true) ->
	  Format.print_string "trace of ";
	  Format.open_box 0;
	  pp_agent 0 a;
	  Format.close_box();
	  Format.print_newline();
	  Agent.trace_left#print (function (a,p) -> "-"^(string_of_action 0 a)^"-> "^(string_of_agent 0 p));
	  Format.print_string "trace of ";
	  Format.open_box 0;
	  pp_agent 0 b;
	  Format.close_box();
	  Format.print_newline();
	  Agent.trace_right#print (function (a,p) -> "-"^(string_of_action 0 a)^"-> "^(string_of_agent 0 p));
	  Format.print_newline();
	  if (flush_entries pp_agent_meta) then Format.force_newline() 
      | _ -> ()
		

let rec handle_command = function
    Def(s,a) -> 
      begin
	let fn = Agent.free_names env a in
	  if Agent.NameSet.is_empty fn then
	    begin
	      env#add_agent s a;
	      Format.print_string ("Agent "^s^" is defined.");
	      Format.print_newline()
	    end
	  else
	    begin
	      Format.print_string ("Agent "^s^" is not defined because there are free variables:");
	      Agent.NameSet.iter (function n -> Format.print_string (" "^(Pprinter.string_of_var 0 n))) fn;
	      Format.print_newline()
	    end
      end
  | Exit -> exit 0
  | Eqd(l,a,b) ->
      begin
	let fn = Agent.NameSet.union (Agent.free_names env a) (Agent.free_names env b) in
	let l = Agent.NameSet.elements (Agent.NameSet.inter (Agent.set_of_list l) fn) in
	let d = Agent.dist_of_lists l (Agent.NameSet.elements fn) in
	let (n,bisim) = Agent.eq env a b d in
	  (match n with
	       0 -> 
		 Format.print_string ("The two agents are not strongly related ("^(string_of_int (max Agent.trace_left#length Agent.trace_right#length))^").");
		 Format.print_newline();
		 see_trace a b
	     | n -> 
		 Format.print_string ("The two agents are strongly related ("^(string_of_int n)^").");
		 Format.print_newline();
		 see_bisim bisim
	  );
      end
  | Weqd(l,a,b) ->
      begin
	let fn = Agent.NameSet.union (Agent.free_names env a) (Agent.free_names env b) in
	let l = Agent.NameSet.elements (Agent.NameSet.inter (Agent.set_of_list l) fn) in
	let d = Agent.dist_of_lists l (Agent.NameSet.elements fn) in
	let (n,bisim) = Agent.weq env a b d in
	  (match n with
	       0 -> 
		 Format.print_string ("The two agents are not weakly related ("^(string_of_int (max Agent.trace_left#length Agent.trace_right#length))^").");
		 Format.print_newline();
		 see_trace a b
	     | n -> 
		 Format.print_string ("The two agents are weakly related ("^(string_of_int n)^").");
		 Format.print_newline();
		 see_bisim bisim
	  );
      end
  | Show(a) -> 
      begin
	Format.open_box 0;
	pp_agent 0 (Agent.standard_form env 0 a);
	Format.close_box();
	Format.print_newline()
      end
  | Print(a) ->
      begin
	Format.open_box 0;
	pp_agent 0 a;
	Format.close_box();
	Format.print_newline()
      end
  | Latex(a) ->
      begin
	Format.open_box 0;
	pp_agent_latex 0 a;
	Format.close_box();
	Format.print_newline()
      end
  | Reset ->
      begin
	Agent_parse.helper#reset;
	env#reset;
	Format.print_string "Reinitialised.";
	Format.print_newline()
      end
  | Clear(ids) ->
      begin
	Format.print_string "Clearing ";
	pp_list_string ids;
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
		     Format.print_string s;
		     Format.print_newline();
		     batch lexer
		   end
	       | Parsing.Parse_error ->
		   begin
		     Format.print_newline();
		     Format.print_string "Parse error";
		     Format.print_newline();
		     Format.print_string "Aborting...";
		     Format.print_newline();
		   end
	       | Lexer.Eof
	       | End_of_file -> () (* Format.print_string "End of file";Format.print_newline() *)
	       | Not_found ->
		   begin
		     Format.print_string "Something is not defined.";
		     Format.print_newline();
		     batch lexer
		   end
	       | Agent.Not_defined(s) ->
		   begin
		     Format.print_string ("Agent "^s^" is not defined.");
		     Format.print_newline();
		     batch lexer
		   end
	       | e -> 
		   begin
		     Format.print_string "Oops... unexpected error";
		     Format.print_newline();
		     raise e;
		     batch lexer
		   end)
	  in
	  let in_descr=Unix.openfile f [Unix.O_RDONLY] 0 in	  
	  let in_channel=Unix.in_channel_of_descr in_descr in
	    batch (lexer (Lexing.from_channel in_channel));
	    Unix.close in_descr
	in
	  Format.print_string ("Opening file "^f);Format.print_newline();
	  (try
	     read_file f;
	     Format.print_string ("Closing file "^f);Format.print_newline();
	   with
	       Unix.Unix_error(_) -> 
		 Format.print_string ("Error while opening file...");Format.print_newline ())
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
	Format.print_string "Pushing ";
	pp_list_var 0 l;
	List.iter (function x -> Agent_parse.helper#push x) l;
      end
  | Pop(n) ->
      begin
	Format.print_string ("Popping at most "^(string_of_int n)^" variables.");
	Format.print_newline();
	Agent_parse.helper#pop n;
      end;
  | Implicit ->
      begin
	match (Agent_parse.helper#get_current_context) with
	    [] -> 
	      Format.print_string "No implicit variables.";
	      Format.print_newline()
	  | l -> 
	      Format.print_string "Implicit variables are ";
	      pp_list_var 0 l
      end
  | Nocommand -> ()
  | Help ->
      begin
	Format.print_string ("ABC v. "^(Compile_info.version));Format.print_newline ();
	Format.print_string ("build on "^(Compile_info.build_info)^" on the "^(Compile_info.date_of_compile));Format.print_newline ();
	Format.print_string "---";Format.print_newline ();
	Format.print_string "agent <Name[(params)]> = <agent>";Format.print_newline();
	Format.print_string "- define the agent <Name(params)> with the body <agent>";Format.print_newline();
	Format.print_string "eq <agent1> <agent2>";Format.print_newline();
	Format.print_string "- check strong equivalence between <agent1> and <agent2>";Format.print_newline();
	Format.print_string "eqd <(v1,...,vn)> <agent1> <agent2>";Format.print_newline();
	Format.print_string "- check strong equivalence between <agent1> and <agent2> with distinction pwd(v1,...,vn,fn agent1,fn agent2)";Format.print_newline();
	Format.print_string "weq <agent1> <agent2>";Format.print_newline();
	Format.print_string "- check weak equivalence between <agent1> and <agent2>";Format.print_newline();
	Format.print_string "weqd <(v1,...,vn)> <agent1> <agent2>";Format.print_newline();
	Format.print_string "- check weak equivalence between <agent1> and <agent2> with distinction pwd(v1,...,vn,fn agent1,fn agent2)";Format.print_newline();
	Format.print_string "show <agent>";Format.print_newline();
	Format.print_string "- show standard form of <agent>";Format.print_newline();
	Format.print_string "print <agent>";Format.print_newline();
	Format.print_string "- (pretty-)print <agent>";Format.print_newline();
	Format.print_string "latex <agent>";Format.print_newline();
	Format.print_string "- generate LaTeX code for <agent> (use some LaTeX macros)";Format.print_newline();
	Format.print_string "step <agent>";Format.print_newline();
	Format.print_string "- interactive exploration of the commitments of <agent>";Format.print_newline();
	Format.print_string "reset";Format.print_newline();
	Format.print_string "- reinitialise the workbench";Format.print_newline();
	Format.print_string "exit";Format.print_newline();
	Format.print_string "- exit the workbench";Format.print_newline();
	Format.print_string "help";Format.print_newline();
	Format.print_string "- this help";Format.print_newline();
      end
  | Rate(n) ->
      if (0 <= n) && (n <= !Agent.max_rate) then
	begin
	  Agent.buffer_switch n;
	  Format.print_string ("Caching rate is now "^(string_of_int !Agent.buffer_rate)^"/"^(string_of_int (!Agent.max_rate))^".");
	end
      else
	Format.print_string "Invalid rate.";
      Format.print_newline();
  | Maxrate(n) ->
      if n > 0 then
	begin
	  Agent.set_maxrate n;
	  Format.print_string ("Caching rate is now "^(string_of_int !Agent.buffer_rate)^"/"^(string_of_int (!Agent.max_rate))^".");
	end
      else
	Format.print_string "Invalid bound.";
      Format.print_newline()
  | _ ->
      begin
	Format.print_string "Not yet implemented.";
	Format.print_newline();
      end

let welcome () = 
  Format.print_string "Welcome to Another Bisimulation Checker";
  Format.print_newline()

let _ =
  welcome();
  let rec loop () = 
    (try
       Format.print_string "abc > ";Format.print_flush ();
       let com = parse_command lexer_stdin in
	 handle_command com;
	 loop ()
     with
	 Failure(s) -> 
	   begin
	     Format.print_string s;
	     Format.print_newline();
	     loop ()
	   end
       | Parsing.Parse_error ->
	   begin
	     Format.print_newline();
	     Format.print_string "Parse error";
	     Format.print_newline();
	     loop ()
	   end
       | Lexer.Eof
       | End_of_file ->
	   begin
	     Format.print_newline();
	     Format.print_string "Bye bye !";
	     Format.print_newline();
	     exit 0
	   end
       | Not_found ->
	   begin
	     Format.print_string "Something is not defined.";
	     Format.print_newline();
	     loop ()
	   end
       | Agent.Not_defined(s) ->
	   begin
	     Format.print_string ("Agent "^s^" is not defined.");
	     Format.print_newline();
	     loop ()
	   end
       | e -> 
	   begin
	     Format.print_string "Oops... unexpected error";
	     Format.print_newline();
	     raise e;
	     loop ()
	   end)
  in
    loop ()

