open Z3utils

module Map = struct
  type t = BitVec.t

  let len = 32

  let big_int_map = BitVecVal.from_int ~len 0

  let boolean_map = BitVecVal.from_int ~len 1

  let fixed_array_map = BitVecVal.from_int ~len 2

  let fixed_double_array_map = BitVecVal.from_int ~len 3

  let weak_fixed_array_map = BitVecVal.from_int ~len 4

  let heap_number_map = BitVecVal.from_int ~len 5
end

let map_of ptr mem = Memory.load ptr 4 mem

let has_map_of map ptr mem = Value.eq (map_of ptr mem) map

let is_big_int ptr mem = Value.eq (map_of ptr mem) Map.big_int_map

let is_boolean ptr mem = Value.eq (map_of ptr mem) Map.boolean_map

let is_fixed_array ptr mem = Value.eq (map_of ptr mem) Map.fixed_array_map

let is_fixed_double_array ptr mem =
  Value.eq (map_of ptr mem) Map.fixed_double_array_map

let is_weak_fixed_array ptr mem =
  Value.eq (map_of ptr mem) Map.weak_fixed_array_map

let is_heap_number ptr mem = Value.eq (map_of ptr mem) Map.heap_number_map

module HeapNumber = struct
  type t = { map : BitVec.t; value : BitVec.t }

  let number_len = 64

  let size = (Map.len + number_len) / 8

  let map_offset = 0

  let number_offset = Map.len / 8

  let allocate = Memory.allocate (size |> BitVecVal.from_int ~len:Value.len)

  let from_number_string s =
    { map = Map.heap_number_map; value = s |> BitVecVal.from_f64string }

  let from_value value = { map = Map.heap_number_map; value }

  let store ptr obj cond mem =
    mem := Memory.store ptr (Map.len / 8) cond obj.map !mem;
    mem :=
      Memory.store
        (Pointer.movei ptr number_offset)
        (number_len / 8) cond obj.value !mem

  let load ptr mem =
    {
      map = Memory.load ptr (Map.len / 8) mem;
      value = Memory.load (Pointer.movei ptr number_offset) (number_len / 8) mem;
    }

  let map_of obj = obj.map

  let number_of obj = obj.value

  let is_zero obj = BitVec.eqb obj.value (BitVecVal.zero ())

  let is_minus_zero obj = BitVec.eqb obj.value (BitVecVal.minus_zero ())

  let is_nan obj = BitVec.eqb obj.value (BitVecVal.nan ())

  let is_ninf obj = BitVec.eqb obj.value (BitVecVal.ninf ())

  let is_inf obj = BitVec.eqb obj.value (BitVecVal.inf ())

  let is_integer obj =
    BitVec.eqb obj.value
      (obj.value |> Float.from_ieee_bv |> Float.round Float.rne_mode
     |> Float.to_ieee_bv)

  let is_safe_integer obj =
    let value_in_float = obj.value |> Float.from_ieee_bv in
    Bool.ands
      [
        is_integer obj;
        Float.ge value_in_float (Float.safe_integer_min ());
        Float.le value_in_float (Float.safe_integer_max ());
      ]
end
