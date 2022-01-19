exception Invalid_type of string * string

type t = Id of string | Const of string

let of_id id = Id id
let of_const v = Const v

let to_int operand =
  match operand with Id id -> int_of_string id | Const v -> int_of_string v

let to_str operand = match operand with Id id -> "#" ^ id | Const v -> v

let err excpt =
  (match excpt with
  | Invalid_type (c, r) -> Printf.fprintf stderr "Type mismatch: %s\n%s\n\n" c r
  | _ -> ());
  raise excpt

(* operands *)
let get_nth_id operands idx =
  let operand = List.nth operands idx in
  match operand with
  | Id id -> id
  | _ ->
      err
        (Invalid_type
           ( operand |> to_str,
             Printf.sprintf "`%s` doesn't have type `ID`" (operand |> to_str) ))

let str_of_operands operands =
  List.fold_left (fun res operand -> res ^ (operand |> to_str)) "" operands
