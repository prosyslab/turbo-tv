open Z3utils

module HeapNumber = struct
  type t = { map : BitVec.t; value : BitVec.t }

  let number_len = 64

  let size = (Objmap.len + number_len) / 8

  let map_offset = 0

  let number_offset = Objmap.len / 8

  let allocate bid =
    Memory.allocate bid (size |> BitVecVal.from_int ~len:Value.len)

  let from_number_string s =
    { map = Objmap.heap_number_map; value = s |> BitVecVal.from_f64string }

  let from_value value = { map = Objmap.heap_number_map; value }

  let store ptr obj cond mem =
    mem := Memory.store ptr (Objmap.len / 8) cond obj.map !mem;
    mem :=
      Memory.store
        (Pointer.movei ptr number_offset)
        (number_len / 8) cond obj.value !mem

  let load ptr mem =
    {
      map = Memory.load ptr (Objmap.len / 8) mem;
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

  let to_string model obj =
    Format.sprintf "HeapNumber(%s)"
      (obj.value |> Model.eval model |> Float.from_ieee_bv |> Float.to_real
     |> Expr.to_simplified_string)
end

let map_of ptr mem = Memory.load ptr 4 mem

let has_map_of map ptr mem = Value.eq (map_of ptr mem) map

let is_big_int ptr mem = Value.eq (map_of ptr mem) Objmap.big_int_map

let is_boolean ptr mem = Value.eq (map_of ptr mem) Objmap.boolean_map

let is_fixed_array ptr mem = Value.eq (map_of ptr mem) Objmap.fixed_array_map

let is_fixed_double_array ptr mem =
  Value.eq (map_of ptr mem) Objmap.fixed_double_array_map

let is_weak_fixed_array ptr mem =
  Value.eq (map_of ptr mem) Objmap.weak_fixed_array_map

let is_heap_number ptr mem =
  Bool.ands
    [
      Z3utils.BitVec.eqi (ptr |> Pointer.size_of) HeapNumber.size;
      Z3utils.BitVec.eqi (ptr |> Pointer.off_of) 0;
      Value.eq (map_of ptr mem) Objmap.heap_number_map;
    ]

let to_string model mem ptr =
  let map = map_of ptr mem in
  let map_str = map |> Objmap.to_string model in
  match map_str with
  | "heap_number" ->
      let obj = HeapNumber.load ptr mem in
      HeapNumber.to_string model obj
  | _ ->
      failwith
        (Format.sprintf "Objects.to_string: not implemented for map '%s'"
           map_str)
