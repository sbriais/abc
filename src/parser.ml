open Lexer

class ['a,'b] lexer (lexfun:'a->'b) (lexbuf:'a) =
object(self)
  val mutable next_tokens = []
  method top_token = 
    match next_tokens with
	[] -> 
	  let t = lexfun lexbuf in
	    next_tokens <- [t];
	    t
      | t::_ -> t
  method pop_token = 
    let t = self#top_token in
      next_tokens <- List.tl next_tokens;
      t
  method peek_token i =
    let rec aux accu = function
	1 -> 
	  let t = self#top_token in
	    self#push_token accu;t
      | n when n > 0 ->
	  aux (self#pop_token::accu) (n-1)
      | _ -> failwith "cannot look backward"
    in aux [] i
  method push_token l =
    let rec push = function
	[] -> ()
      | t::ts ->
	  next_tokens <- t::next_tokens;
	  push ts
    in push l
end

let warn s = 
  Format.print_string ("WARNING: "^s);
  Format.print_newline()

let parse_token t lexer error =
  if lexer#pop_token = t then ()
  else error ()

let rec parse_until_token t lexer =
  parse_token t lexer (function () -> parse_until_token t lexer)

let parse_error lexer str =
  parse_until_token EOL lexer;
  failwith str

let intelligent_parsing s tokens lexer k_ok k_fail =
  let warning s token adv =
    warn (s^" "^adv^" means "^((function Some(s) -> s) (reverse token)))
  in
    (match (find_nearest s (keywords tokens)) with
	 Some(d,t) ->
	   (if d <= 0.5 then
	      begin
		warning s t "certainly";
		let _ = lexer#push_token [t] in k_ok ()
	      end
	    else
	      if d <= 1.0 then
		begin
		  warning s t "probably";
		  let _ = lexer#push_token [t] in k_ok ()
		end
	      else
		begin
		  warning s t "maybe";
		  warn "I don't try to continue.";
		  k_fail ()
		end)
       | _ -> k_fail ())

let rec yes_no lexer =
  match lexer#pop_token with
      YES -> 
	parse_token EOL lexer (function () -> parse_until_token EOL lexer;failwith "Please follow your answer by <enter>.");
	true
    | NO ->
	parse_token EOL lexer (function () -> parse_until_token EOL lexer;failwith "Please follow your answer by <enter>.");
	false
    | IDENT(s)
    | VAR(s) ->
	(*
	  (match find_nearest s (keywords [YES;NO]) with
	  Some(d,t) ->
	  if d <= 1. then
	  let _ = lexer#push_token [t] in 
	  warn (s^" probably means "^((function Some(s) -> s) (reverse t)));
	  yes_no lexer
	  else 
	  parse_error lexer "Please answer by yes or no followed by <enter>."
	  | _ -> parse_error lexer "Please answer by yes or no followed by <enter>.")
	*)
	intelligent_parsing s [YES;NO] lexer (function () -> yes_no lexer) (function () -> parse_error lexer "Please answer by yes or no followed by <enter>.")
    | _ -> 
	parse_error lexer "Please answer by yes or no followed by <enter>."
	
let number lexer = 
  match lexer#pop_token with
      INT(n) -> 
	parse_token EOL lexer (function () -> parse_until_token EOL lexer;failwith "Please follow your answer by <enter>.");
	n
    | _ ->
	parse_error lexer "Please answer by a number followed by <enter>."	

let rec agent lexer =
  let f = agent_facteur lexer in
    match lexer#top_token with
	PLUS ->
	  let _ = lexer#pop_token in
	  let s = agent lexer in
	    (match s with
		 Agent.Sum(terms) -> Agent.Sum(Agent.AgentMultiset.add f 1 terms)
	       | _ -> Agent.Sum(Agent.AgentMultiset.add f 1 (Agent.AgentMultiset.singleton s)))
      | _ -> f
and agent_facteur lexer = 
  let g = agent_garde lexer in
    match lexer#top_token with
	PAR ->
	  let _ = lexer#pop_token in
	  let p = agent_facteur lexer in
	    (match p with
		 Agent.Parallel(factors) -> Agent.Parallel(Agent.AgentMultiset.add g 1 factors)
	       | _ -> Agent.Parallel(Agent.AgentMultiset.add g 1 (Agent.AgentMultiset.singleton p)))
      | _ -> g
and agent_garde lexer =
  let ag = agent_garde2 lexer in
  let rec apply_var ag =
    match lexer#top_token with
	VAR(x) ->
	  let _ = lexer#pop_token in
	    apply_var (Agent.Apply(ag,Agent_parse.helper#get x))
      | _ -> ag
  in apply_var ag
and agent_garde2 lexer =
  match lexer#top_token with
      NIL
    | INT(0) -> 
	let _ = lexer#pop_token in
	  Agent.Nil
    | IDENT(name) ->
	let _ = lexer#pop_token in
	let p = params lexer in
	  List.fold_left (fun a v -> Agent.Apply(a,v)) (Agent.AgentRef(name)) ((Agent_parse.helper#get_context name)@p)
    | LPAREN ->
	let _ = lexer#pop_token in
	  (match lexer#top_token with
	       LAMBDA ->
		 let _ = lexer#pop_token in
		 let xs = vars lexer in
		   (match lexer#top_token with
			RPAREN -> 
			  let _ = lexer#pop_token in
			  let a = agent_garde lexer in
			    List.fold_right (fun n a -> Agent.Abs(Agent.add_binder n a)) xs a
		      | _ -> parse_error lexer "Missing ) symbol in lambda abstraction.")
	     | NU ->
		 let _ = lexer#pop_token in
		 let xs = vars lexer in
		   (match lexer#top_token with
			RPAREN -> 
			  let _ = lexer#pop_token in
			  let a = agent_garde lexer in
			    List.fold_right (fun n a -> Agent.Nu(Agent.add_binder n a)) xs a
		      | _ -> parse_error lexer "Missing ) symbol in nu abstraction.")
	     | _ ->
		 let a = agent lexer in
		   (match lexer#top_token with
			RPAREN -> 
			  let _ = lexer#pop_token in a
		      | _ -> parse_error lexer "Missing ) symbol."))
    | TAU ->
	let _ = lexer#pop_token in
	  (match lexer#top_token with
	       DOT ->
		 let _ = lexer#pop_token in
		 let ag = agent_garde lexer in
		   Agent.Prefix(Agent.Tau,ag)
	     | _ -> 
		 (* parse_error lexer "Missing . symbol." *)
		 Agent.Prefix(Agent.Tau,Agent.Nil))
    | VAR(x) ->
	let _ = lexer#pop_token in
	let vs = params lexer in
	  (match lexer#top_token with
	       DOT ->
		 let _ = lexer#pop_token in
		 let ag = agent_garde lexer in
		   Agent.Prefix(Agent.Input(Agent_parse.helper#get x),
				List.fold_right (fun n a -> Agent.Abs(Agent.add_binder n a)) vs ag)
	     | _ -> 
		 (* parse_error lexer "Missing . symbol." *)
		 Agent.Prefix(Agent.Input(Agent_parse.helper#get x),
			      List.fold_right (fun n a -> Agent.Abs(Agent.add_binder n a)) vs Agent.Nil))
    | OUTPUT ->
	let _ = lexer#pop_token in
	  (match lexer#top_token with
	       VAR(x) ->
		 let _ = lexer#pop_token in
		 let vs = oparams lexer in
		   (match lexer#top_token with
			DOT ->
			  let _ = lexer#pop_token in
			  let ag = agent_garde lexer in
			    Agent.Prefix(Agent.Output(Agent_parse.helper#get x),
					 List.fold_right (fun n a -> Agent.Conc(n,a)) vs ag)
		      | _ -> 
			  (* parse_error lexer "Missing . symbol." *)
			  Agent.Prefix(Agent.Output(Agent_parse.helper#get x),
				       List.fold_right (fun n a -> Agent.Conc(n,a)) vs Agent.Nil))
	     | _ -> parse_error lexer "I was expecting a name.")
    | LBRACKET ->
	let _ = lexer#pop_token in
	  (match lexer#peek_token 2 with
	       EQUAL ->
		 (match lexer#top_token with
		      VAR(x) ->
			let _ = lexer#pop_token in
			  (match lexer#top_token with
			       EQUAL -> 
				 let _ = lexer#pop_token in
				   (match lexer#top_token with
					VAR(y) -> 
					  let _ = lexer#pop_token in
					    (match lexer#top_token with
						 RBRACKET ->
						   let _ = lexer#pop_token in
						   let ag = agent_garde lexer in
						     Agent.Match(Agent_parse.helper#get x,
								 Agent_parse.helper#get y,ag)
					       | _ -> parse_error lexer "Missing ] symbol.")
				      | _ -> parse_error lexer "I was expecting another name.")
			     | _ -> failwith "Inconsistent error.")
		    | _ -> parse_error lexer "I was expecting a name.")
	     | _ ->
		 let vs = vars lexer in
		   (match lexer#top_token with
			RBRACKET -> 
			  let _ = lexer#pop_token in
			  let ag = agent_garde lexer in
			    List.fold_right (fun n a -> Agent.Conc(n,a)) vs ag
		      | _ -> parse_error lexer "Missing ] symbol."))
    | _ -> parse_error lexer "Error while parsing agent."
and vars lexer =
  match lexer#top_token with
      VAR(x) ->
	let x = Agent_parse.helper#get x in
	let _ = lexer#pop_token in
	  (match lexer#top_token with
	       COMMA -> 
		 let _ = lexer#pop_token in
		   x::(vars lexer)
	     | _ -> [x])
    | _ -> parse_error lexer "I was expecting at least one variable name."
and vars_space lexer =
  let rec aux accu =
    match lexer#top_token with
	VAR(x) ->
	  let x = Agent_parse.helper#get x in
	  let _ = lexer#pop_token in
	    aux (x::accu)
      | _ ->
	  if accu = [] then
	    parse_error lexer "I was expecting at least one variable name."
	  else List.rev accu
  in
    aux []
and ident_space lexer =
  let rec aux accu =
    match lexer#top_token with
	IDENT(x) ->
	  let _ = lexer#pop_token in
	    aux (x::accu)
      | _ ->
	  if accu = [] then
	    parse_error lexer "I was expecting at least one agent name."
	  else List.rev accu
  in
    aux []
and params lexer =
  match lexer#top_token with
      LPAREN -> 
	let _ = lexer#pop_token in
	let xs = vars lexer in
	  (match lexer#top_token with
	       RPAREN -> 
		 let _ = lexer#pop_token in xs
	     | _ -> 
		 parse_error lexer "Missing ) symbol.")
    | _ -> []
and oparams lexer = 
  match lexer#top_token with
      LESS -> 
	let _ = lexer#pop_token in
	let xs = vars lexer in
	  (match lexer#top_token with
	       GT -> 
		 let _ = lexer#pop_token in xs
	     | _ -> 
		 parse_error lexer "Missing > symbol.")
    | _ -> []
and agent_signature lexer =
  match lexer#top_token with
      IDENT(s) ->
	let _ = lexer#pop_token in
	let p =
	  (match lexer#top_token with
	       VAR(_) -> vars_space lexer
	     | _ -> params lexer) in (s,p)
    | _ ->
	parse_error lexer "Wrong agent signature (missing name)."

let rec command lexer = 
  match lexer#pop_token with
      EXIT ->
	parse_token EOL lexer (function () -> parse_error lexer "Please follow your command by <enter>.");
	Commands.Exit
    | RESET ->
	parse_token EOL lexer (function () -> parse_error lexer "Please follow your command by <enter>.");
	Commands.Reset
    | HELP ->
	parse_token EOL lexer (function () -> parse_error lexer "Please follow your command by <enter>.");
	Commands.Help
    | IMPLICIT ->
	parse_token EOL lexer (function () -> parse_error lexer "Please follow your command by <enter>.");
	Commands.Implicit
    | EOL -> Commands.Nocommand
    | PRINT ->
	let c = Commands.Print(agent lexer) in
	  parse_token EOL lexer (function () -> parse_error lexer "Please follow your command by <enter>.");
	  c
    | SHOW ->
	let c = Commands.Show(agent lexer) in
	  parse_token EOL lexer (function () -> parse_error lexer "Please follow your command by <enter>.");
	  c
    | STEP ->
	let c = Commands.Step(agent lexer) in
	  parse_token EOL lexer (function () -> parse_error lexer "Please follow your command by <enter>.");
	  c
    | LATEX ->
	let c = Commands.Latex(agent lexer) in
	  parse_token EOL lexer (function () -> parse_error lexer "Please follow your command by <enter>.");
	  c
    | RATE ->
	(match lexer#top_token with
	     INT(n) ->
	       let _ = lexer#pop_token in
		 parse_token EOL lexer (function () -> parse_error lexer "Please follow your command by <enter>.");
		 Commands.Rate(n)
	   | _ ->
	       parse_error lexer "The command 'value' should be followed by a positive integer.")
    | MAXRATE ->
	(match lexer#top_token with
	     INT(n) ->
	       let _ = lexer#pop_token in
		 parse_token EOL lexer (function () -> parse_error lexer "Please follow your command by <enter>.");
		 Commands.Maxrate(n)
	   | _ ->
	       parse_error lexer "The command 'scale' should be followed by a positive integer.")
    | LOAD ->
	(match lexer#top_token with
	     VAR(s)
	   | IDENT(s)
	   | FILENAME(s) ->
	       let _ = lexer#pop_token in
		 parse_token EOL lexer (function () -> parse_error lexer "Please follow your command by <enter>.");
		 Commands.Load(s)
	   | _ -> 
	       parse_error lexer "The command 'load' should be followed by a file name.") 
    | POP ->
	(match lexer#top_token with
	     INT(n) ->
	       let _ = lexer#pop_token in
		 parse_token EOL lexer (function () -> parse_error lexer "Please follow your command by <enter>.");
		 Commands.Pop(n)
	   | _ ->
	       parse_token EOL lexer (function () -> parse_error lexer "Please follow your command by <enter>.");
	       Commands.Pop(1))
    | PUSH ->
	let vars = vars_space lexer in
	  parse_token EOL lexer (function () -> parse_error lexer "Please follow your command by <enter>.");
	  Commands.Push(vars)
    | EQ ->
	let a1 = agent lexer in
	let a2 = agent lexer in
	  parse_token EOL lexer (function () -> parse_error lexer "Please follow your command by <enter>.");
	  Commands.Eqd([],a1,a2)
    | EQD ->
	let d = params lexer in
	let a1 = agent lexer in
	let a2 = agent lexer in
	  parse_token EOL lexer (function () -> parse_error lexer "Please follow your command by <enter>.");
	  Commands.Eqd(d,a1,a2)
    | WEQ ->
	let a1 = agent lexer in
	let a2 = agent lexer in
	  parse_token EOL lexer (function () -> parse_error lexer "Please follow your command by <enter>.");
	  Commands.Weqd([],a1,a2)
    | WEQD ->
	let d = params lexer in
	let a1 = agent lexer in
	let a2 = agent lexer in
	  parse_token EOL lexer (function () -> parse_error lexer "Please follow your command by <enter>.");
	  Commands.Weqd(d,a1,a2)
    | AGENT ->
	let (name,params) = agent_signature lexer in
	  (match lexer#top_token with
	       EQUAL ->
		 let _ = lexer#pop_token in
		   Agent_parse.helper#define name;
		   (try
		      let agent = agent lexer in
			parse_token EOL lexer (function () -> parse_error lexer "Please follow your command by <enter>.");
			Commands.Def(name,List.fold_right (fun n a -> Agent.Abs(Agent.add_binder n a)) ((Agent_parse.helper#get_context name)@params) agent)
		    with e -> Agent_parse.helper#undefine name;raise e)
	     | _ ->
		 parse_error lexer "Missing = symbol in agent definition.")
    | CLEAR ->
	let ids = ident_space lexer in
	  parse_token EOL lexer (function () -> parse_error lexer "Please follow your command by <enter>.");
	  Commands.Clear(ids);
    | IDENT(s) 
    | VAR(s) ->
	(*
	  (match find_nearest s (keywords [EXIT;RESET;HELP;IMPLICIT;PRINT;SHOW;STEP;LATEX;RATE;MAXRATE;LOAD;POP;PUSH;EQ;EQD;WEQ;WEQD;AGENT;CLEAR]) with
	  Some(d,t) ->
	  if d <= 1. then
	  let _ = lexer#push_token [t] in 
	  warn (s^" probably means "^((function Some(s) -> s) (reverse t)));
	  command lexer
	  else 
	  parse_error lexer "Invalid command."
	  | _ -> parse_error lexer "Invalid command.")
	*)
	intelligent_parsing s [EXIT;RESET;HELP;IMPLICIT;PRINT;SHOW;STEP;LATEX;RATE;MAXRATE;LOAD;POP;PUSH;EQ;EQD;WEQ;WEQD;AGENT;CLEAR] lexer (function () -> command lexer) (function () -> parse_error lexer "Invalid command.")
    | _ -> 
	parse_error lexer "Invalid command."
