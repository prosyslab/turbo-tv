open Z3utils

type t = BitVec.t

let len = 32

let size = 4

let big_int_map = BitVecVal.from_int ~len 0

let boolean_map = BitVecVal.from_int ~len 1

let fixed_array_map = BitVecVal.from_int ~len 2

let fixed_double_array_map = BitVecVal.from_int ~len 3

let weak_fixed_array_map = BitVecVal.from_int ~len 4

let heap_number_map = BitVecVal.from_int ~len 5

let undefined_map = BitVecVal.from_int ~len 6

let null_map = BitVecVal.from_int ~len 7

let oddball_map = BitVecVal.from_int ~len 8

let string_map = BitVecVal.from_int ~len 9

let custom_map n = BitVecVal.from_int ~len n

let names = [ "Map[12](HEAP_NUMBER_TYPE)" ]

let is_known_map name = List.mem name names

let map_of name =
  match name with
  | "Map[12](HEAP_NUMBER_TYPE)" -> heap_number_map
  | _ -> failwith (Format.sprintf "not implemented: %s" name)

let to_string model t =
  let map_bstr = t |> Model.eval model |> Expr.to_string in
  let map =
    try
      "0" ^ String.sub map_bstr 1 (String.length map_bstr - 1)
      |> Int32.of_string |> Int32.unsigned_to_int |> Option.get
    with _ -> -1
  in
  match map with
  | 0 -> "big_int"
  | 1 -> "boolean"
  | 2 -> "fixed_array"
  | 3 -> "fixed_double_array"
  | 4 -> "weak_fixed_array"
  | 5 -> "heap_number"
  | 6 -> "undefined"
  | 7 -> "null"
  | 8 -> "oddball"
  | 9 -> "string"
  | _ -> Format.sprintf "unknown(map:0x%x)" map
