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
(* File lexer.mll *)
{
  type token =
      VAR of (string)
    | IDENT of (string)
    | FILENAME of (string)
    | INT of (int)
    | NU
    | LAMBDA
    | DOT
    | OUTPUT
    | TAU
    | NIL
    | COMMA
    | LBRACKET
    | RBRACKET
    | GT
    | LESS
    | LPAREN
    | RPAREN
    | PAR
    | PLUS
    | EQUAL
    | EOL
    | YES
    | NO
    | AGENT
    | EQ
    | WEQ
    | LT
    | WLT
    | EXIT
    | SHOW
    | EQD
    | WEQD
    | LTD
    | WLTD
    | PRINT
    | RESET
    | STEP
    | LATEX
    | HELP
    | RATE
    | MAXRATE
    | LOAD
    | PUSH
    | POP
    | IMPLICIT
    | INVALID
    | CLEAR

  exception Eof

  let keyword_table = Hashtbl.create 20
  let _ =
    List.iter (fun (kwd, tok) -> Hashtbl.add keyword_table kwd tok)
      [ "agent", AGENT;
	"t", TAU;
	"eq", EQ;
	"weq", WEQ;
	"exit",EXIT;
	"show",SHOW;
	"eqd", EQD;
	"weqd", WEQD;
	"lt",LT;
	"wlt",WLT;
	"reset", RESET;
	"print", PRINT;
	"step", STEP;
	"latex",LATEX;
	"help", HELP;
	"value",RATE;
	"scale",MAXRATE;
	"load",LOAD;
	"push",PUSH;
	"pop",POP;
	"implicit",IMPLICIT;
	"yes", YES;
	"no", NO;
	"clear", CLEAR
      ]

  let plsc x y =
    let m = String.length x
    and n = String.length y in
    let c = Array.make_matrix (m+1) (n+1) 0 in
      for i = 1 to m do
	for j = 1 to n do
          if (String.get x (i-1)) = (String.get y (j-1)) then
            c.(i).(j) <- c.(i-1).(j-1) + 1
          else
	    c.(i).(j) <- max (c.(i-1).(j)) (c.(i).(j-1))
	done
      done;
      c.(m).(n)

  let c_inserer = 1
  let c_supprimer = 1
  let c_remplacement x y =
    if (Char.uppercase x) = (Char.uppercase y) then 0 else 1
  let c_permuter = 1
  let c_init i j = 
    if (i <= 1) || (j <= 1) then 1 else 0

  let distance x y =
    let m = String.length x
    and n = String.length y in
    let c = Array.make_matrix (m+1) (n+1) 0 in
      for i = 1 to m do
	c.(i).(0) <- (c_init i 0) + c_supprimer * i;
      done;
      for j = 1 to n do
	c.(0).(j) <- (c_init 0 j) + c_inserer * j;
      done;
      for i = 1 to m do
	for j = 1 to n do
          let cout = (c_init i j) + (min (c.(i-1).(j) + c_supprimer) (c.(i).(j-1) + c_inserer)) in
	  let cx = String.get x (i-1) and cy = String.get y (j-1) in
	  let cout =
            if (i >= 2) && (j >= 2) then
              if (cx = (String.get y (j-2))) && ((String.get x (i-2)) = cy) then
		min (c.(i-2).(j-2) + c_permuter) cout
              else cout
            else cout
          in
	  let c_r = c_remplacement cx cy in
	    if c_r = 0 then
	      c.(i).(j) <- min (c.(i-1).(j-1)) cout
	    else
	      c.(i).(j) <- min ((c.(i-1).(j-1)) + c_r + (c_init i j)) cout
	done;
      done;
      c.(m).(n)

  exception Found of string

  let reverse t =
    (try
       Hashtbl.iter (fun k t' -> if t = t' then raise (Found(k))) keyword_table;
       None
     with
	Found(k) -> Some(k))

  let keywords ts =
    List.map (function Some(t) -> t | _ -> failwith "Impossible.") (List.filter (function None -> false | _ -> true) (List.map (function t -> reverse t) ts))

  let heuristic_dist x y =
    let delta x y =
      match (String.length x) - (String.length y) with
	  n when n >= 0 -> n
	| n -> -n
    in
      (float_of_int (distance x y)) /. (float_of_int (1+(plsc x y)))

  let find_nearest s ks =
    let (dmin,ts) = List.fold_left (fun (dmin,ts) k ->
				      let d' = heuristic_dist s k in
					match dmin with
					    None -> (Some(d'),[k])
					  | Some(d) ->
					      if d' < d then (Some(d'),[k])
					      else 
						if d' = d then (Some(d),k::ts)
						else (Some(d),ts)) (None,[]) ks
    in
      (match dmin with
	   None -> None
	 | Some(d) ->
	     (match ts with
		  [k] -> Some(d,Hashtbl.find keyword_table k)
		| _ -> None))

  let (init,enter,exit,is_toplevel) = 
    let counter = ref 0 in
    let init () = counter := 0
    and enter () = incr counter
    and exit () = decr counter
    and is_toplevel () = (!counter) = 0
    in (init,enter,exit,is_toplevel)
}

rule command = parse
    [' ' '\t']     { command lexbuf }     (* skip blanks *)
  | '\\'[' ''\t']*'\n'         { command lexbuf }
  | "(*"           { init();enter();comments lexbuf }
  | '\n'           { EOL }
  | ['a'-'z']['/''_''A'-'Z''a'-'z''0'-'9']*  { let s = Lexing.lexeme lexbuf in
						 (try
						    Hashtbl.find keyword_table s
						  with
						      Not_found -> VAR(s))
					     }
  | ['A'-'Z']['/''_''A'-'Z''a'-'z''0'-'9']*  { IDENT(Lexing.lexeme lexbuf) }
  | ['0'-'9']+     { INT(int_of_string(Lexing.lexeme lexbuf)) }
  | '"'[^'"']*'"'  { let name = Lexing.lexeme lexbuf in
		       FILENAME(String.sub name 1 ((String.length name)-2))
		   }
  | '^'            { NU }
  | '\\'           { LAMBDA }
  | '.'            { DOT }
  | '\''           { OUTPUT }
  | '|'            { PAR }
  | '+'            { PLUS }
  | '='            { EQUAL }
  | '['            { LBRACKET }
  | ']'            { RBRACKET }
  | '('            { LPAREN }
  | ')'            { RPAREN }
  | ','            { COMMA }
  | '<'            { LESS }
  | '>'            { GT }
  | '0'            { NIL }
  | eof            { raise Eof }
  | _              { INVALID }
and comments = parse
    "(*"           { enter();comments lexbuf }
  | "*)"           { exit();if (is_toplevel ()) then (command lexbuf) else (comments lexbuf) }
  | _              { comments lexbuf }
