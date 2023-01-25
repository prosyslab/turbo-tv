let pow b e = float_of_int b ** float_of_int e |> int_of_float

let check_bracket_match left right =
  match (left, right) with '(', ')' | '[', ']' | '<', '>' -> true | _ -> false

let contains s1 s2 =
  let re = Str.regexp_string s2 in
  try
    ignore (Str.search_forward re s1 0);
    true
  with Not_found -> false
