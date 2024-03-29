open Z3utils
open ValueOperator

type t = { map : BitVec.t; value : BitVec.t }

let number_len = 64

let size = (Objmap.len + number_len) / 8

let map_offset = 0

let number_offset = Objmap.len / 8

let allocate mem =
  Memory.allocate (size |> BitVecVal.from_int ~len:Value.len) mem

let from_number_string s =
  { map = Objmap.heap_number_map; value = s |> BitVecVal.from_f64string }

let store ptr cond obj mem =
  (* ptr is tagged *)
  mem
  |> Memory.Bytes.store cond
       (ptr |> TaggedPointer.to_raw_pointer)
       (Objmap.len / 8) obj.map
  |> Memory.Bytes.store cond
       (TaggedPointer.movei ptr number_offset |> TaggedPointer.to_raw_pointer)
       (number_len / 8) obj.value

let load ptr mem =
  {
    map =
      Memory.Bytes.load
        (ptr |> TaggedPointer.to_raw_pointer)
        (Objmap.len / 8) mem;
    value =
      Memory.Bytes.load
        (TaggedPointer.movei ptr number_offset |> TaggedPointer.to_raw_pointer)
        (number_len / 8) mem;
  }

let from_float64 cond mem value_f64 =
  let ptr, mem = allocate mem in
  let obj =
    { map = Objmap.heap_number_map; value = value_f64 |> Value.data_of }
  in
  let mem = store ptr cond obj mem in
  (ptr, mem)

let to_float64 obj = obj.value |> Value.entype Type.float64

let to_int64 obj = obj.value |> Float64.to_int64

let map_of obj = obj.map

let number_of obj = obj.value

let is_zero obj = Float.is_zero (obj.value |> Float.from_ieee_bv)

let is_minus_zero obj = Float.is_minus_zero (obj.value |> Float.from_ieee_bv)

let is_nan obj = Float.is_nan (obj.value |> Float.from_ieee_bv)

let is_ninf obj = Float.is_ninf (obj.value |> Float.from_ieee_bv)

let is_inf obj = Float.is_inf (obj.value |> Float.from_ieee_bv)

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
    else
      Format.sprintf "%s (raw: %s)"
        (evaluated |> Real.to_decimal_string)
        (evaluated |> Expr.to_simplified_string)
  in

  Format.sprintf "HeapNumber(%s)" f_str
