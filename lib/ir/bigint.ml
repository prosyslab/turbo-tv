open Z3utils
open ValueOperator

let sign_field_bytes = 1

let length_field_bytes = 4

type t = { map : BitVec.t; sign : BitVec.t; value : BitVec.t }

let create sign value = { map = Objmap.big_int_map; sign; value }

let allocate_big_int ?(size = 8) t mem =
  let sign = t.sign in
  let ptr, mem = Memory.allocate (Value.from_int (Objmap.size + size)) mem in
  let big_int_value = t.value in
  let mem =
    mem
    |> Memory.store Bool.tr
         (ptr |> TaggedPointer.to_raw_pointer)
         Objmap.size Objmap.big_int_map
    |> Memory.store Bool.tr
         (TaggedPointer.movei ptr Objmap.size |> TaggedPointer.to_raw_pointer)
         sign_field_bytes sign
    |> Memory.store Bool.tr
         (TaggedPointer.movei ptr (Objmap.size + sign_field_bytes)
         |> TaggedPointer.to_raw_pointer)
         size big_int_value
  in
  (ptr, mem)

let parse_big_int_const name mem =
  let sign_and_values = name |> String.split_on_char ' ' |> List.tl in
  let sign =
    (if String.equal (List.hd sign_and_values) "+" then 0 else 1)
    |> BitVecVal.from_int ~len:8
  in
  let values = List.tl sign_and_values in
  let length = List.length values in
  let size = length * 8 in
  let big_int_value =
    values
    |> List.map (fun s -> BitVecVal.from_istring_trunc s)
    |> Composed.from_values
  in
  allocate_big_int ~size (create sign big_int_value) mem

let load ptr mem =
  let map = Memory.load (ptr |> TaggedPointer.to_raw_pointer) Objmap.size mem in
  let sign =
    Memory.load
      (TaggedPointer.movei ptr Objmap.size |> TaggedPointer.to_raw_pointer)
      sign_field_bytes mem
  in
  let value =
    Memory.load
      (TaggedPointer.movei ptr (Objmap.size + sign_field_bytes)
      |> TaggedPointer.to_raw_pointer)
      8 mem
  in
  { map; sign; value }

let is_negative t =
  let sign = t.sign in
  BitVec.eqb (BitVecVal.from_int ~len:8 1) sign

let to_int64 t =
  Bool.ite (is_negative t) (BitVec.subb (BitVecVal.zero ()) t.value) t.value
  |> Value.entype Type.int64
