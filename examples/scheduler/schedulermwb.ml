let rec insert x = function
    [] -> [x]
  | y::ys -> 
      if x < y then x::y::ys
      else 
	if x = y then y::ys
	else y::(insert x ys)

let rec sub x = function
    [] -> []
  | y::ys ->
      if x < y then y::ys
      else 
	if x = y then ys
	else y::(sub x ys)

let str_of_int n p =
  let s = string_of_int p in
  let m = n - (String.length s) in
    (String.make (max m 0) '0')^s

let rec str_of_list n = function
    [] -> ""
  | x::xs -> (str_of_int n x)^(str_of_list n xs)

let round x = int_of_float (floor (x +. 0.5))

let log10 x = (log x)/.(log 10.)
 
let fig n = 1+(round (log10 (float_of_int n)))

let vars n sep = 
  let rec vars c n = function
      0 -> ""
    | i ->
	let s = vars c n (i-1) in
	  c^(str_of_int (fig n) (i mod n))^
	  (if s = "" then ""
	   else sep)^s
  in
    (vars "a" n n)^sep^(vars "b" n n)

let schedu i n xs =
  "Sched"^(str_of_int (fig n) (i mod n))^(str_of_list (fig n) xs)^" "^(vars n " ")

let schedu2 i n xs =
  "Sched"^(str_of_int (fig n) (i mod n))^(str_of_list (fig n) xs)^"("^(vars n ",")^")"

let schedu = schedu2

let rec sched i n xs =
  let i = i mod n in
  let rec sum i = function
      [] -> ""
    | j::js ->
	"b"^(str_of_int (fig n) j)^"."^(schedu i n (sub j xs))^
	(let s = (sum i js) in 
	   if s = "" then ""
	   else " + "^s)
  in
    if List.mem i xs then
      sum i xs
    else
      (let s = (sum i xs) in
	 (if s = "" then ""
	  else s^" + ")^
	 "a"^(str_of_int (fig n) i)^"."^(schedu (i+1) n (insert i xs)))

let proc s n i =
  s^" a"^((str_of_int (fig n) (i mod n)))^" b"^(str_of_int (fig n) (i mod n))^" c"^(str_of_int (fig n) (i mod n))^" c"^(str_of_int (fig n) ((i-1) mod n))

let proc2 s n i =
  s^"(a"^((str_of_int (fig n) (i mod n)))^",b"^(str_of_int (fig n) (i mod n))^",c"^(str_of_int (fig n) (i mod n))^",c"^(str_of_int (fig n) ((i-1) mod n))^")"

let proc = proc2

let def_a = "agent A(a,b,c,d) = a.C(a,b,c,d)"
let def_b = "agent B(a,b,c,d) = b.A(a,b,c,d)"
let def_c = "agent C(a,b,c,d) = c.E(a,b,c,d)"
let def_d = "agent D(a,b,c,d) = 'd.A(a,b,c,d)"
let def_e = "agent E(a,b,c,d) = (b.D(a,b,c,d) + 'd.B(a,b,c,d))"
  
let s n =
  let rec vars n = function
      0 -> ""
    | i ->
	let s = vars n (i-1) in
	  "c"^(str_of_int (fig n) (i mod n))^
	  (if s = "" then ""
	   else ",")^s
  in
  let rec ds n = function
      2 -> proc "D" n 2
    | i ->
	(ds n (i-1))^" | "^(proc "D" n i)
  in
    "(^"^(vars n n)^")("^(proc "A" n 1)^" | "^(ds n n)^")"

let rec set = function
    0 -> []
  | n -> (set (n-1))@[n-1] 

let rec powerset = function
    [] -> [[]]
  | x::xs ->
      let p = powerset xs in
	p@(List.map (insert x) p)

let spec i n =
  List.iter (function xs -> print_string ("agent "^(schedu2 i n xs)^" = ("^(sched i n xs)^")");print_newline()) (powerset (set n))

let gen_sched n =
  print_string def_a;print_newline();
  print_string def_b;print_newline();
  print_string def_c;print_newline();
  print_string def_d;print_newline();
  print_string def_e;print_newline();
  print_string ("agent S("^(vars n ",")^") = "^(s n));print_newline();
  print_string ("agent Scheduler("^(vars n ",")^") = "^(schedu 1 n []));print_newline();
  for i = 1 to n do
    spec i n
  done;
  print_string ("weqd ("^(vars n ",")^") Scheduler("^(vars n ",")^")"^" S("^(vars n ",")^")");print_newline()

let _ =
  let n = int_of_string (input_line stdin) in
    gen_sched n

