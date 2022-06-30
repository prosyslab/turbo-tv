let pow b e = float_of_int b ** float_of_int e |> int_of_float

let check_bracket_match left right =
  match (left, right) with '(', ')' | '[', ']' | '<', '>' -> true | _ -> false