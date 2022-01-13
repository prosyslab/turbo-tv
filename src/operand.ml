type t = Int of int | Bool of bool

let to_string operand =
  match operand with Int i -> Int.to_string i | Bool b -> Bool.to_string b

let str_of_operands operands =
  let res =
    List.fold_left
      (fun res operand -> String.concat ", " [ res; operand |> to_string ])
      "(" operands
  in
  res ^ ")"

let of_int i = Int i
let of_bool b = Bool b
