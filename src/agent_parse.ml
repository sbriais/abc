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
