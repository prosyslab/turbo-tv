type t = Id of int | Const of string

let of_id id = Id id
let of_const v = Const v
let id_of_str str = int_of_string str |> of_id
let const_of_str str = str |> of_const

let to_string operand =
  match operand with Id id -> "#" ^ Int.to_string id | Const v -> v

let str_of_operands operands =
  List.fold_left (fun res operand -> res ^ (operand |> to_string)) "" operands
