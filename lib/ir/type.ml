open Z3utils

type t = BitVec.t

let len = 5

let smi_min = -1073741824

let smi_max = 1073741823

let smi_mask = 0xffffffff

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
