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
  | Ltd of Name.t list * Agent.agent * Agent.agent
  | Wltd of Name.t list * Agent.agent * Agent.agent
  | Push of (Name.t list)
  | Pop of int
  | Clear of (string list)
  | List of (command list)
