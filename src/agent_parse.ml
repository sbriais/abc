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
exception Found of string

(* table des symboles *)
class parse_helper =
object(self)
  val vars = Hashtbl.create 10
  val agents = Hashtbl.create 10
  val mutable context = []
  val mutable counter = Name.zero
  method private new_var = 
    counter <- Name.succ counter
  method reset =
    Hashtbl.clear vars;
    counter <- Name.zero;
    Hashtbl.clear agents;
    context <- []
  method get (s:string) =
    (try
       Hashtbl.find vars s
     with
	 Not_found ->
	   self#new_var;
	   Hashtbl.add vars s counter;
	   counter)
  method reverse (n:Name.t) =
    (try
       Hashtbl.iter 
	 (fun s m -> if (Name.compare n m = 0) then raise (Found(s)))
	 vars;
       None
     with
	 Found(s) -> Some(s))
  method push (x:Name.t) =
    context <- x::context;
    Hashtbl.iter (fun s (k,l) -> incr l) agents
  method private pop1 = 
    Hashtbl.iter (fun s (k,l) ->
		    if !l > 0 then decr l
		    else
		      begin
			assert(!l = 0);
			if !k > 0 then decr k
			else 			
			  assert(!k = 0);
		      end) agents
  method pop n =
    (try
       for i = 1 to n do
	 context <- List.tl context;
       done;
     with _ -> ());
    for i = 1 to n do
      self#pop1
    done;
  method define (s:string) =
    (* cache la valeur précédente *)
    Hashtbl.add agents s ((ref (List.length context)),ref 0)
  method undefine (s:string) =
    (* efface la dernière valeur mise *)
    Hashtbl.remove agents s
  method get_context (s:string) =
    (try
       let k = !(fst (Hashtbl.find agents s)) in
       let rec get_n n = function
	   [] -> []
	 | x::xs -> if n <= 0 then [] else x::(get_n (n-1) xs)
       in
	 get_n k (List.rev context)
     with Not_found -> List.rev context)
  method get_current_context = List.rev context
  method clear (s:string) =
    while Hashtbl.mem agents s do
      Hashtbl.remove agents s
    done
end

let helper = new parse_helper
