open Z3utils

type t = BitVec.t

let len = 5

(* type-constants *)
(* v8 types *)
let int8 = BitVecVal.from_int ~len 0

let uint8 = BitVecVal.from_int ~len 1

let int16 = BitVecVal.from_int ~len 2

let uint16 = BitVecVal.from_int ~len 3

let int32 = BitVecVal.from_int ~len 4

let uint32 = BitVecVal.from_int ~len 5

let int64 = BitVecVal.from_int ~len 6

let uint64 = BitVecVal.from_int ~len 7

let float32 = BitVecVal.from_int ~len 8

let float64 = BitVecVal.from_int ~len 9

let simd128 = BitVecVal.from_int ~len 10

let pointer = BitVecVal.from_int ~len 11

let tagged_pointer = BitVecVal.from_int ~len 12

let map_in_header = BitVecVal.from_int ~len 13

let tagged_signed = BitVecVal.from_int ~len 14

let any_tagged = BitVecVal.from_int ~len 15

let compressed_pointer = BitVecVal.from_int ~len 16

let any_compressed = BitVecVal.from_int ~len 17

let sandboxed_pointer = BitVecVal.from_int ~len 18

let bool = BitVecVal.from_int ~len 19

let none = BitVecVal.from_int ~len 20

let empty = BitVecVal.from_int ~len 21

let const = BitVecVal.from_int ~len 22

let int_types = [ int8; int16; int32; int64 ]

let uint_types = [ uint8; uint16; uint32; uint64 ]

let float_types = [ float32; float64 ]

let to_string model t =
  let ty_in_binstring =
    let ty_str = t |> Model.eval model |> Expr.to_simplified_string in
    "0" ^ String.sub ty_str 1 (String.length ty_str - 1)
  in
  match ty_in_binstring |> int_of_string with
  | 0 -> "int8"
  | 1 -> "uint8"
  | 2 -> "int16"
  | 3 -> "uint16"
  | 4 -> "int32"
  | 5 -> "uint32"
  | 6 -> "int64"
  | 7 -> "uint64"
  | 8 -> "float32"
  | 9 -> "float64"
  | 10 -> "simd128"
  | 11 -> "pointer"
  | 12 -> "tagged_pointer"
  | 13 -> "map_in_header"
  | 14 -> "tagged_signed"
  | 15 -> "any_tagged"
  | 16 -> "compressed_pointer"
  | 17 -> "any_compressed"
  | 18 -> "sandboxed_pointer"
  | 19 -> "bool"
  | 20 -> "none"
  | 21 -> "empty"
  | 22 -> "const"
  | _ -> failwith "unreachable"

(* ty from MachineType *)
let from_machine_type (mt : MachineType.t) =
  match mt with
  | Int8 -> int8
  | Uint8 -> uint8
  | Int16 -> int16
  | Uint16 -> uint16
  | Int32 -> int32
  | Uint32 -> uint32
  | Int64 -> int64
  | Uint64 -> uint64
  | Float32 -> float32
  | Float64 -> float64
  | Simd128 -> simd128
  | Pointer -> pointer
  | TaggedPointer -> tagged_pointer
  | MapInHeader -> map_in_header
  | TaggedSigned -> tagged_signed
  | AnyTagged -> any_tagged
  | CompressedPointer -> compressed_pointer
  | AnyCompressed -> any_compressed
  | SandboxedPointer -> sandboxed_pointer
  | Bool -> bool
  | None -> none

let from_repr (repr : MachineType.Repr.t) =
  List.map from_machine_type (MachineType.of_repr repr)
