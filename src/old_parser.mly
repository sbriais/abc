/* File parser.mly */
%{
  let fail s n =
    failwith ("Error after "
	      ^
	      s
(*
	      ^
	      " at position "
	      ^(string_of_int ((rhs_start n)))
*)
	     )
%}

%token <string> VAR
%token <string> IDENT
%token <int> INT
%token NU LAMBDA DOT OUTPUT TAU NIL COMMA
%token LBRACKET RBRACKET GT LESS
%token LPAREN RPAREN
%token PAR PLUS EQUAL
%token EOL
%token YES NO
%token AGENT EQ WEQ EXIT SHOW EQD WEQD PRINT RESET STEP LATEX HELP RATE MAXRATE LOAD
%token INVALID
%left PLUS
%left PAR
%start command             /* the entry point */
%start yes_no
%start number
%type <Commands.command> command
%type <bool> yes_no
%type <int> number
%%

command:
AGENT IDENT EQUAL agent EOL       { Commands.Def($2,$4) }
| AGENT IDENT LPAREN vars RPAREN EQUAL agent EOL { Commands.Def($2,List.fold_right (fun n a -> Agent.Abs(Agent.add_binder n a)) $4 $7) } 
| EQ agent agent EOL              { Commands.Eqd([],$2,$3) }
| WEQ agent agent EOL             { Commands.Weqd([],$2,$3) }
| EQD LPAREN vars RPAREN agent agent EOL 
                                  { Commands.Eqd($3,$5,$6) }
| WEQD LPAREN vars RPAREN agent agent EOL 
                                  { Commands.Weqd($3,$5,$6) }
| EXIT EOL                        { Commands.Exit }
| RESET EOL                       { Commands.Reset }
| HELP EOL                        { Commands.Help }
| RATE INT EOL                    { Commands.Rate($2) }
| MAXRATE INT EOL                 { Commands.Maxrate($2) }
| SHOW agent EOL                  { Commands.Show($2) }
| PRINT agent EOL                 { Commands.Print($2) }
| LATEX agent EOL                 { Commands.Latex($2) }
| STEP agent EOL                  { Commands.Step($2) }
| LOAD VAR EOL                    { Commands.Load($2) }

| AGENT error EOL                 { fail "AGENT" 2 }
| AGENT IDENT error EOL           { fail "AGENT IDENT" 3 }
| AGENT IDENT EQUAL error EOL     { fail "AGENT IDENT EQUAL" 4 }
| AGENT IDENT LPAREN error EOL    { fail "AGENT IDENT LPAREN" 4 }
| AGENT IDENT LPAREN vars error EOL { fail "AGENT IDENT LPAREN vars" 5 }
| AGENT IDENT LPAREN vars RPAREN error EOL { fail "AGENT IDENT LPAREN vars RPAREN" 4 }
| AGENT IDENT LPAREN vars RPAREN EQUAL error EOL { fail "AGENT IDENT LPAREN vars RPAREN EQUAL" 7 }
| EQ error EOL                    { fail "EQ" 2 }
| EQ agent error EOL              { fail "EQ agent" 3 }
| WEQ error EOL                   { fail "WEQ" 2 }
| WEQ agent error EOL             { fail "WEQ agent" 3 }
| SHOW error EOL                  { fail "SHOW" 2 }
| PRINT error EOL                 { fail "PRINT" 2 }
| LATEX error EOL                 { fail "LATEX" 2 }
| STEP error EOL                  { fail "STEP" 2 }
| EQD error EOL                   { fail "EQD" 2 }
| EQD LPAREN error EOL            { fail "EQD LPAREN" 3 }
| EQD LPAREN vars error EOL       { fail "EQD LPAREN vars" 4 }
| EQD LPAREN vars RPAREN error EOL { fail "EQD LPAREN vars RPAREN" 5 }
| EQD LPAREN vars RPAREN agent error EOL { fail "EQD LPAREN vars RPAREN agent" 6 }
| WEQD error EOL                  { fail "WEQD" 2 }
| WEQD LPAREN error EOL           { fail "WEQD LPAREN" 3 }
| WEQD LPAREN vars error EOL      { fail "WEQD LPAREN vars" 4 }
| WEQD LPAREN vars RPAREN error EOL { fail "WEQD LPAREN vars RPAREN" 5 }
| WEQD LPAREN vars RPAREN agent error EOL { fail "WEQD LPAREN vars RPAREN agent" 6 }
| error EOL                       { failwith "Invalid command." }
;

agent:
NIL                            { Agent.Nil }
| INT                          { if $1 = 0 then Agent.Nil else raise Parse_error }
| prefix DOT agent             { Agent.Prefix($1,$3) }
| VAR LPAREN vars RPAREN DOT agent 
                               { Agent.Prefix(Agent.Input(Agent_parse.get $1),List.fold_right (fun n a -> Agent.Abs(Agent.add_binder n a)) $3 $6) }
| OUTPUT VAR LESS vars GT DOT agent 
                               { Agent.Prefix(Agent.Output(Agent_parse.get $2),List.fold_right (fun n a -> Agent.Conc(n,a)) $4 $7) }
| TAU error                    { fail "TAU" 2 }
| VAR error                    { fail "VAR" 2 }
| VAR LPAREN error             { fail "VAR LPAREN" 3 }
| VAR LPAREN vars error        { fail "VAR LPAREN vars" 4 }
| VAR LPAREN vars RPAREN error { fail "VAR LPAREN vars RPAREN" 5 }
| VAR LPAREN vars RPAREN DOT error { fail "VAR LPAREN vars RPAREN DOT" 6 }
| OUTPUT error                 { fail "OUTPUT" 2 }
| OUTPUT VAR error             { fail "OUTPUT VAR" 3 }
| OUTPUT VAR LESS error        { fail "OUTPUT VAR LESS" 4 }
| OUTPUT VAR LESS vars error   { fail "OUTPUT VAR LESS vars" 5 }
| OUTPUT VAR LESS vars GT error   { fail "OUTPUT VAR LESS vars GT" 6 }
| OUTPUT VAR LESS vars GT DOT error   { fail "OUTPUT VAR LESS vars GT DOT" 7 }

| LBRACKET VAR RBRACKET agent  { Agent.Conc(Agent_parse.get $2,$4) }
| LBRACKET VAR EQUAL VAR RBRACKET agent { Agent.Match(Agent_parse.get $2,Agent_parse.get $4,$6) }

| LBRACKET error               { fail "LBRACKET" 2 }
| LBRACKET VAR error           { fail "LBRACKET VAR" 3 }
| LBRACKET VAR RBRACKET error  { fail "LBRACKET VAR RBRACKET" 4 }
| LBRACKET VAR EQUAL error        { fail "LBRACKET VAR EQUAL" 4 }
| LBRACKET VAR EQUAL VAR error    { fail "LBRACKET VAR EQUAL VAR" 5 }
| LBRACKET VAR EQUAL VAR RBRACKET error    { fail "LBRACKET VAR EQUAL VAR RBRACKET" 6 }

| LPAREN LAMBDA vars RPAREN agent { List.fold_right (fun n a -> Agent.Abs(Agent.add_binder n a)) $3 $5 }
| LPAREN NU vars RPAREN agent     { List.fold_right (fun n a -> Agent.Nu(Agent.add_binder n a)) $3 $5 }

/*
| LPAREN LAMBDA vars RPAREN DOT agent { List.fold_right (fun n a -> Agent.Abs(Agent.add_binder n a)) $3 $6 }
| LPAREN NU vars RPAREN DOT agent     { List.fold_right (fun n a -> Agent.Nu(Agent.add_binder n a)) $3 $6 }
*/

/*
| LAMBDA VAR DOT agent         { Agent.Abs(Agent.add_binder (Agent_parse.get $2) $4) }

| LAMBDA error                 { fail "LAMBDA" 2 }
| LAMBDA VAR error             { fail "LAMBDA VAR" 3 }
| LAMBDA VAR DOT error         { fail "LAMBDA VAR DOT" 4 }

| NU VAR DOT agent             { Agent.Nu(Agent.add_binder (Agent_parse.get $2) $4) }

| NU error                     { fail "NU" 2 }
| NU VAR error                 { fail "NU VAR" 3 }
| NU VAR DOT error             { fail "NU VAR DOT" 4 }
*/

| LPAREN sums RPAREN           { Agent.Sum($2) }
| LPAREN pars RPAREN           { Agent.Parallel($2) }

| LPAREN error                 { fail "LPAREN" 2 }
| LPAREN sums error            { fail "LPAREN sums" 3 }
| LPAREN pars error            { fail "LPAREN pars" 3 }
| LPAREN LAMBDA error          { fail "LPAREN LAMBDA" 3 }
| LPAREN LAMBDA vars error     { fail "LPAREN LAMBDA vars" 4 }
| LPAREN LAMBDA vars RPAREN error     { fail "LPAREN LAMBDA vars" 5 }
/*
| LPAREN LAMBDA vars RPAREN DOT error { fail "LPAREN LAMBDA vars" 6 }
*/
| LPAREN NU error              { fail "LPAREN NU" 3 }
| LPAREN NU vars error         { fail "LPAREN NU vars" 4 }
| LPAREN NU vars RPAREN error     { fail "LPAREN NU vars" 5 }
/*
| LPAREN NU vars RPAREN DOT error { fail "LPAREN NU vars" 6 }
*/

| IDENT                        { Agent.AgentRef($1) }

| IDENT LPAREN vars RPAREN     { List.fold_left (fun a v -> Agent.Apply(a,v)) (Agent.AgentRef($1)) $3 }
      
| agent VAR                    { Agent.Apply($1,Agent_parse.get $2) }

| agent error                  { fail "agent" 2 }
;

sums:
  agent                        { Agent.AgentMultiset.singleton $1 }
| agent PLUS sums              { Agent.AgentMultiset.add $1 1 $3 }
| agent PLUS error             { fail "agent PLUS" 3 }
;

pars:
  agent                        { Agent.AgentMultiset.singleton $1 }
| agent PAR pars               { Agent.AgentMultiset.add $1 1 $3 }
| agent PAR error              { fail "agent PAR" 3 }
;

prefix:
VAR                            { Agent.Input(Agent_parse.get $1) }
| OUTPUT VAR                   { Agent.Output(Agent_parse.get $2) }
| TAU                          { Agent.Tau }
;

vars:
VAR                            { [Agent_parse.get $1] }
| vars COMMA VAR               { $1@[Agent_parse.get $3] }
| vars COMMA error             { fail "vars COMMA" 3 }
;

iparams:
/* epsilon */                  { [] }
| LPAREN vars RPAREN           { $2 }
;

oparams:
/* epsilon */                  { [] }
| LESS vars GT                 { $2 }
;

yes_no:
YES EOL                        { true }
| NO EOL                       { false}
| error EOL                    { failwith "Answer with yes or no." 1 }
;

number:
INT EOL                        { $1 }
| error EOL                    { failwith "Answer with a number." 1 }
;
