class ['a] arbreMutable (elem:'a) =
  let indente n = print_string (String.make n ' ') in
object(self)
  val mutable sons = []
  val mutable father = None
  method setFather f = father <- Some(f)
  method newSon son = 
    try
      self#getSon son 
    with
	Not_found ->
	  let fils = new arbreMutable son in
	    fils#setFather (self:>'a arbreMutable);
	    sons <- fils::sons;
	    fils
  method removeSon son =
    sons <- List.filter (function fils -> fils#getElem <> son) sons
  method private getSon son =
    List.find (function fils -> fils#getElem = son) sons
  method getElem = elem
  method getFather = father
  method print toString = self#pp toString false 0
  method pp toString b n =
    if not b then indente n;
    let elemStr = if self#isRoot then "" else (toString elem) in
    let elemLen = String.length elemStr in
      print_string elemStr;
      indente 1;
      if self#isLeaf then
	print_newline()
      else
	ignore (List.fold_left (fun b fils -> fils#pp toString b (n+1+elemLen);false) true sons)
  method isLeaf =
    match sons with
	[] -> true
      | _ -> false
  method isRoot =
    match father with
	None -> true
      | _ -> false
end
