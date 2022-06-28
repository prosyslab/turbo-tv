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

  let store ptr obj cond mem =
    (* ptr is tagged *)
    mem :=
      Memory.store
        (ptr |> TaggedPointer.to_raw_pointer)
        (Objmap.len / 8) cond obj.map !mem;
    mem :=
      Memory.store
        (TaggedPointer.movei ptr number_offset |> TaggedPointer.to_raw_pointer)
        (number_len / 8) cond obj.value !mem

  let load ptr mem =
    {
      map =
        Memory.load (ptr |> TaggedPointer.to_raw_pointer) (Objmap.len / 8) mem;
      value =
        Memory.load
          (TaggedPointer.movei ptr number_offset |> TaggedPointer.to_raw_pointer)
          (number_len / 8) mem;
    }

  let from_float64 bid cond value_f64 mem =
    let ptr = allocate bid in
    let obj =
      { map = Objmap.heap_number_map; value = value_f64 |> Value.data_of }
    in
    store ptr obj cond mem;
    ptr

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
    let f_str =
      let fval = obj.value |> Float.from_ieee_bv |> Model.eval model in
      let is_nan =
        fval |> Float.is_nan |> Expr.to_simplified_string |> bool_of_string
      in
      let is_minus_zero =
        fval |> Float.is_minus_zero |> Expr.to_simplified_string
        |> bool_of_string
      in
      let is_inf =
        fval |> Float.is_minus_zero |> Expr.to_simplified_string
        |> bool_of_string
      in
      let is_ninf =
        fval |> Float.is_minus_zero |> Expr.to_simplified_string
        |> bool_of_string
      in

      if is_nan then "NaN"
      else if is_minus_zero then "-0.0"
      else if is_inf then "Infinity"
      else if is_ninf then "-Infinity"
      else fval |> Real.to_decimal_string
    in
    Format.sprintf "HeapNumber(%s)" f_str
end

let map_of ptr mem = Memory.load (ptr |> TaggedPointer.to_raw_pointer) 4 mem

let has_map_of map ptr mem = Value.eq (map_of ptr mem) map

let is_big_int ptr mem = Value.eq (map_of ptr mem) Objmap.big_int_map

let is_boolean ptr mem = Value.eq (map_of ptr mem) Objmap.boolean_map

let is_fixed_array ptr mem = Value.eq (map_of ptr mem) Objmap.fixed_array_map

let is_fixed_double_array ptr mem =
  Value.eq (map_of ptr mem) Objmap.fixed_double_array_map

let is_weak_fixed_array ptr mem =
  Value.eq (map_of ptr mem) Objmap.weak_fixed_array_map

let is_heap_number ptr mem = Value.eq (map_of ptr mem) Objmap.heap_number_map

let to_string model mem ptr =
  let map = map_of ptr mem in
  let map_str = map |> Objmap.to_string model in
  match map_str with
  | "heap_number" ->
      let obj = HeapNumber.load ptr mem in
      HeapNumber.to_string model obj
  | s -> s ^ " object: not implemented yet"
