type command = 
  | Exit
  | Reset
  | Help
  | Nocommand
  | Implicit
  | Show of Agent.agent
  | Print of Agent.agent
  | Step of Agent.agent 
  | Latex of Agent.agent
  | Rate of int
  | Maxrate of int
  | Load of string
  | Def of string * Agent.agent
  | Eqd of Name.t list * Agent.agent * Agent.agent
  | Weqd of Name.t list * Agent.agent * Agent.agent
  | Push of (Name.t list)
  | Pop of int
  | Clear of (string list)
