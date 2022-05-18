open Err

module Operand = struct
  type t = Id of string | Const of string

  let of_id id = Id id

  let of_const v = Const v

  let is_id operand = match operand with Id _ -> true | _ -> false

  let is_const operand = match operand with Const _ -> true | _ -> false

  let to_str operand = match operand with Id id -> "#" ^ id | Const v -> v

  let id operand =
    match operand with
    | Id id -> id
    | _ ->
        let cause = operand |> to_str in
        let reason = Printf.sprintf "Operand %s is not type of `Id`" cause in
        err (TypeMismatch (cause, reason))

  let const operand =
    match operand with
    | Const v -> v
    | _ ->
        let cause = operand |> to_str in
        let reason = Printf.sprintf "Operand %s is not type of `Const`" cause in
        err (TypeMismatch (cause, reason))

  let c_as_int const =
    try const |> int_of_string
    with Failure _ ->
      let cause = const in
      let reason = Printf.sprintf "Cannot parse '%s' into `int`" cause in
      err (TypeMismatch (cause, reason))

  let c_as_float const =
    try const |> float_of_string
    with Failure _ ->
      let cause = const in
      let reason = Printf.sprintf "Cannot parse '%s' into `float`" cause in
      err (TypeMismatch (cause, reason))

  let c_as_addr const =
    let re = Re.Pcre.regexp "(0x[0-9a-f]+)" in
    try Re.Group.get (Re.exec re const) 1 |> int_of_string
    with Not_found ->
      let cause = const in
      let reason = Printf.sprintf "Cannot parse '%s' into `addr`" cause in
      err (TypeMismatch (cause, reason))
end

type t = Operand.t list

let to_str operands = String.concat "," (List.map Operand.to_str operands)

let nth operands idx =
  try List.nth operands idx
  with Failure _ | Invalid_argument _ ->
    let reason =
      Printf.sprintf "%d points outside operands: %s" idx (operands |> to_str)
    in
    err (InvalidIndex (idx |> string_of_int, reason))

let rev_nth operands idx =
  try List.nth (operands |> List.rev) idx
  with Failure _ | Invalid_argument _ ->
    let reason =
      Printf.sprintf "%d points outside operands: %s" idx (operands |> to_str)
    in
    err (InvalidIndex (idx |> string_of_int, reason))

let id_of_nth operands idx = nth operands idx |> Operand.id

let const_of_nth operands idx = nth operands idx |> Operand.const

let int_of_nth operands idx =
  nth operands idx |> Operand.const |> Operand.c_as_int

let id_of_all operands =
  List.map (fun operand -> operand |> Operand.id) operands
