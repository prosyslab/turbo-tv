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
    mem
    |> Memory.store
         (ptr |> TaggedPointer.to_raw_pointer)
         (Objmap.len / 8) cond obj.map
    |> Memory.store
         (TaggedPointer.movei ptr number_offset |> TaggedPointer.to_raw_pointer)
         (number_len / 8) cond obj.value

  let load ptr mem =
    {
      map =
        Memory.load (ptr |> TaggedPointer.to_raw_pointer) (Objmap.len / 8) mem;
      value =
        Memory.load
          (TaggedPointer.movei ptr number_offset |> TaggedPointer.to_raw_pointer)
          (number_len / 8) mem;
    }

  let from_float64 bid cond mem value_f64 =
    let next_bid, ptr = allocate bid in
    let obj =
      { map = Objmap.heap_number_map; value = value_f64 |> Value.data_of }
    in
    let mem = store ptr obj cond mem in
    (ptr, next_bid, mem)

  let to_float64 obj = obj.value |> Value.entype Type.float64

  let map_of obj = obj.map

  let number_of obj = obj.value

  let is_zero obj = BitVec.eqb obj.value (BitVecVal.zero ())

  let is_minus_zero obj = BitVec.eqb obj.value (BitVecVal.minus_zero ())

  let is_nan obj = BitVec.eqb obj.value (BitVecVal.nan ())

  let is_ninf obj = BitVec.eqb obj.value (BitVecVal.ninf ())

  let is_inf obj = BitVec.eqb obj.value (BitVecVal.inf ())

  let is_integer obj =
    obj.value |> Value.entype Type.float64 |> Float64.is_integer

  let is_safe_integer obj =
    obj.value |> Value.entype Type.float64 |> Float64.is_safe_integer

  let is_positive obj =
    obj.value |> Value.entype Type.float64 |> Float64.is_positive

  let is_negative obj =
    obj.value |> Value.entype Type.float64 |> Float64.is_negative

  let eq lobj robj = Bool.eq lobj.value robj.value

  let lt lobj robj =
    let l_f64 = lobj |> to_float64 in
    let r_f64 = robj |> to_float64 in
    Float64.lt l_f64 r_f64

  let to_string model obj =
    let f_str =
      let evaluated = obj.value |> Float.from_ieee_bv |> Model.eval model in
      if
        String.contains
          (evaluated |> Float.is_nan |> Expr.to_simplified_string)
          't'
      then "NaN"
      else if
        String.contains
          (evaluated |> Float.is_inf |> Expr.to_simplified_string)
          't'
      then "+oo"
      else if
        String.contains
          (evaluated |> Float.is_ninf |> Expr.to_simplified_string)
          't'
      then "-oo"
      else if
        String.contains
          (evaluated |> Float.is_minus_zero |> Expr.to_simplified_string)
          't'
      then "-0.0"
      else evaluated |> Real.to_decimal_string
    in

    Format.sprintf "HeapNumber(%s)" f_str
end

let map_of ptr mem = Memory.load (ptr |> TaggedPointer.to_raw_pointer) 4 mem

let has_map_of map mem ptr = Bool.eq (map_of ptr mem) map

let is_big_int mem ptr = ptr |> has_map_of Objmap.big_int_map mem

let is_boolean mem ptr = ptr |> has_map_of Objmap.boolean_map mem

let is_fixed_array mem ptr = ptr |> has_map_of Objmap.fixed_array_map mem

let is_fixed_double_array mem ptr =
  ptr |> has_map_of Objmap.fixed_double_array_map mem

let is_weak_fixed_array mem ptr =
  ptr |> has_map_of Objmap.weak_fixed_array_map mem

let is_heap_number mem ptr = ptr |> has_map_of Objmap.heap_number_map mem

let are_heap_nubmer mem ptrs =
  Bool.ands (List.map (has_map_of Objmap.heap_number_map mem) ptrs)

let to_string model mem ptr =
  let map = map_of ptr mem in
  let map_str = map |> Objmap.to_string model in
  match map_str with
  | "heap_number" ->
      let obj = HeapNumber.load ptr mem in
      HeapNumber.to_string model obj
  | s -> s ^ " object: not implemented yet"
