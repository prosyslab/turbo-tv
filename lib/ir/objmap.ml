open Z3utils

type t = BitVec.t

let len = 32

let big_int_map = BitVecVal.from_int ~len 0

let boolean_map = BitVecVal.from_int ~len 1

let fixed_array_map = BitVecVal.from_int ~len 2

let fixed_double_array_map = BitVecVal.from_int ~len 3

let weak_fixed_array_map = BitVecVal.from_int ~len 4

let heap_number_map = BitVecVal.from_int ~len 5

let to_string model t =
  let map_bstr = t |> Model.eval model |> Expr.to_string in
  let map =
    "0" ^ String.sub map_bstr 1 (String.length map_bstr - 1)
    |> Int32.of_string |> Int32.unsigned_to_int |> Option.get
  in
  match map with
  | 0 -> "big_int"
  | 1 -> "boolean"
  | 2 -> "fixed_array"
  | 3 -> "fixed_double_array"
  | 4 -> "weak_fixed_array"
  | 5 -> "heap_number"
  | _ -> Format.sprintf "unknown(map:0x%x)" map
