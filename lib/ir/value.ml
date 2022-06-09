open Z3utils

type t = BitVec.t

(* 1-bit for undef & 5-bit for type & 64-bit for data *)
let undef_len = 1

let ty_len = Type.len

let data_len = 64

let len = undef_len + ty_len + data_len

let size = len / 8

(* getter *)
let ty_of t = BitVec.extract (data_len + ty_len - 1) data_len t

let data_of t = BitVec.extract (data_len - 1) 0 t

let undef_of t = BitVec.extract (len - 1) (len - 1) t

(* cast value [t] to type [ty] *)
let cast ty t =
  if BitVec.length_of t <> len then (
    BitVec.length_of t |> string_of_int |> print_endline;
    failwith "invalid value length")
  else
    let undef = undef_of t in
    BitVec.concat undef (BitVec.concat ty (data_of t))

(* entype [data] to type [ty] *)
let entype ty data =
  let input_data_len = BitVec.length_of data in
  if input_data_len <> data_len then
    failwith (Printf.sprintf "invalid data length: %d" input_data_len)
    (* TODO handling undef of data *)
  else BitVec.concat (BitVecVal.zero ~len:1 ()) (BitVec.concat ty data)

let zero_extend_data data =
  BitVec.zero_extend (data_len - BitVec.length_of data) data

(* constructor *)
let init name = BitVec.init ~len name

let from_int i = BitVecVal.from_int ~len i |> cast Type.const

let from_istring s = BitVecVal.from_istring ~len s |> cast Type.const

let from_f64string s = BitVecVal.from_f64string s |> entype Type.const

let from_bv bv =
  BitVec.zero_extend (len - BitVec.length_of bv) bv |> cast Type.const

let empty = from_int 0 |> cast Type.empty

(* type *)
let has_type ty t = BitVec.eqb (ty_of t) ty

let is_signed_integer t =
  Bool.ors (List.map (fun ty -> has_type ty t) Type.int_types)

let is_unsigned_integer t =
  Bool.ors (List.map (fun ty -> has_type ty t) Type.uint_types)

let is_integer t = Bool.ors [ is_signed_integer t; is_unsigned_integer t ]

let is_float t = Bool.ors (List.map (fun ty -> has_type ty t) Type.float_types)

(* type casting operations *)
let round_float64_to_int32 t =
  data_of t |> Float.from_ieee_bv
  |> Float.to_sbv (Z3.FloatingPoint.RoundingMode.mk_round_toward_zero ctx)
  |> entype Type.int32

let float64_to_int64 t =
  data_of t |> Float.from_ieee_bv
  |> Float.to_sbv (Z3.FloatingPoint.RoundingMode.mk_round_toward_zero ctx)
  |> entype Type.int64

let int32_to_int64 t =
  let x = t |> BitVec.extract 31 0 |> BitVec.sign_extend 32 in
  x |> entype Type.int64

let uint32_to_int64 t = t |> cast Type.int64

let int64_to_float64 t =
  data_of t |> Float.from_signed_bv |> Float.to_ieee_bv |> entype Type.float64

let int32_to_float64 t = t |> int32_to_int64 |> int64_to_float64

let int32_to_int64 t =
  let x = t |> BitVec.extract 31 0 |> BitVec.sign_extend 32 in
  x |> entype Type.int64

let uint32_to_float64 t = t |> uint32_to_int64 |> int64_to_float64

(* representation *)
let has_repr repr t =
  let tys_of_repr = Type.from_repr repr in
  Bool.ors (List.map (fun ty_candid -> has_type ty_candid t) tys_of_repr)

let can_be_float64 s =
  String.contains s '.' || String.equal s "-0" || String.equal s "inf"
  || String.equal s "-inf"

let can_be_smi s =
  try
    let n = int_of_string s in
    Constants.smi_min <= n && n <= Constants.smi_max
    && not (String.equal s "-0")
  with Failure _ -> false

(* type-preserving binary operation *)
let add lval rval =
  let lty = ty_of lval in
  BitVec.addb (data_of lval) (data_of rval) |> entype lty

let addi value i =
  let ty = ty_of value in
  BitVec.addi (data_of value) i |> entype ty

let sub lval rval =
  let lty = ty_of lval in
  BitVec.subb (data_of lval) (data_of rval) |> entype lty

let and_ lval rval =
  let lty = ty_of lval in
  BitVec.andb (data_of lval) (data_of rval) |> entype lty

let andi value mask =
  let ty = ty_of value in
  BitVec.andi (data_of value) mask |> entype ty

let or_ lval rval =
  let lty = ty_of lval in
  BitVec.orb (data_of lval) (data_of rval) |> entype lty

let not_ value =
  let ty = ty_of value in
  BitVec.notb (data_of value) |> entype ty

let shl lval rval =
  let lty = ty_of lval in
  BitVec.shlb (data_of lval) (data_of rval) |> entype lty

let shli value i =
  let ty = ty_of value in
  BitVec.shli (data_of value) i |> entype ty

let lshr lval rval =
  let lty = ty_of lval in
  BitVec.lshrb (data_of lval) (data_of rval) |> entype lty

let ashr lval rval =
  let lty = ty_of lval in
  BitVec.ashrb (data_of lval) (data_of rval) |> entype lty

let xor lval rval =
  let lty = ty_of lval in
  BitVec.xor (data_of lval) (data_of rval) |> entype lty

let mod_ lval rval =
  let lty = ty_of lval in
  BitVec.modb (data_of lval) (data_of rval) |> entype lty

let modi value n = BitVec.modi (data_of value) n |> entype (ty_of value)

let mul lval rval =
  let lty = ty_of lval in
  BitVec.mulb (data_of lval) (data_of rval) |> entype lty

let mask value bitlen = mod_ value (shl (from_int 1) bitlen)

let maski value bitlen = andi value (Int.shift_left 1 bitlen - 1)

(* compare two values and return bool *)
let eq lval rval = BitVec.eqb lval rval

let weak_eq lval rval = BitVec.eqb (data_of lval) (data_of rval)

let slt lval rval = BitVec.sltb (data_of lval) (data_of rval)

let ult lval rval = BitVec.ultb (data_of lval) (data_of rval)

let ulti value i = BitVec.ulti (data_of value) i

let sle lval rval = BitVec.sleb (data_of lval) (data_of rval)

let slei ?(width = len) lval i =
  BitVec.slei (BitVec.extract (width - 1) 0 (data_of lval)) i

let ule lval rval = BitVec.uleb (data_of lval) (data_of rval)

let ulei ?(width = len) lval i =
  BitVec.ulei (BitVec.extract (width - 1) 0 (data_of lval)) i

let ugt lval rval = BitVec.ugtb (data_of lval) (data_of rval)

let ugti value i = BitVec.ugti (data_of value) i

let sge lval rval = BitVec.sgeb (data_of lval) (data_of rval)

let sgei ?(width = len) lval i =
  BitVec.sgei (BitVec.extract (width - 1) 0 (data_of lval)) i

let uge lval rval = BitVec.ugeb (data_of lval) (data_of rval)

let ugei ?(width = len) lval i =
  BitVec.ugei (BitVec.extract (width - 1) 0 (data_of lval)) i

(* Floating Point *)
let geqf lval f =
  (* assmue that lval is integer or float *)
  let lval_f =
    Bool.ite (is_signed_integer lval)
      (Float.from_signed_bv (data_of lval))
      (Bool.ite (is_unsigned_integer lval)
         (Float.from_unsigned_bv (data_of lval))
         (Float.from_ieee_bv (data_of lval)))
  in
  Float.geq lval_f (Float.from_float f)

let leqf lval f =
  (* assmue that lval is integer or float *)
  let lval_f =
    Bool.ite (is_signed_integer lval)
      (Float.from_signed_bv (data_of lval))
      (Bool.ite (is_unsigned_integer lval)
         (Float.from_unsigned_bv (data_of lval))
         (Float.from_ieee_bv (data_of lval)))
  in
  Float.leq lval_f (Float.from_float f)

let addf lval rval =
  let lf = lval |> data_of |> Float.from_ieee_bv in
  let rf = rval |> data_of |> Float.from_ieee_bv in
  Float.add lf rf |> Float.to_ieee_bv |> entype Type.float64

let subf lval rval =
  let lf = lval |> data_of |> Float.from_ieee_bv in
  let rf = rval |> data_of |> Float.from_ieee_bv in
  Float.sub lf rf |> Float.to_ieee_bv |> entype Type.float64

let absf value =
  value |> data_of |> Float.from_ieee_bv |> Float.abs |> Float.to_ieee_bv
  |> entype Type.float64

(* defined & undefined *)
let undefined = BitVec.shli (BitVecVal.from_int ~len 1) (ty_len + data_len)

let is_undefined value = BitVec.eqb undefined (BitVec.andb undefined value)

let is_defined value = Bool.not (is_undefined value)

let set_undefined value = BitVec.orb undefined value

let set_defined value = BitVec.andb (BitVec.notb undefined) value

(* constant values *)

let tr = addi empty 1 |> cast Type.bool

let is_true value = eq tr value

let fl = empty |> cast Type.bool

let is_false value = eq fl value

let zero = BitVecVal.zero () |> entype Type.const

(* IEEE-754 *)
let inf = BitVecVal.inf () |> entype Type.float64

let ninf = BitVecVal.ninf () |> entype Type.float64

let minus_zero = BitVecVal.minus_zero () |> entype Type.float64

let nan = BitVecVal.nan () |> entype Type.float64

(* smi constant values *)
let smi_min = Constants.smi_min |> BitVecVal.from_int |> entype Type.const

let smi_max = Constants.smi_max |> BitVecVal.from_int |> entype Type.const

(* Int32 constant values *)
let int32_min =
  Int32.min_int |> Int32.to_int |> BitVecVal.from_int |> entype Type.const

let int32_max =
  Int32.max_int |> Int32.to_int |> BitVecVal.from_int |> entype Type.const

(* Int64 constant values *)
let int64_min =
  Int64.min_int |> Int64.to_string |> BitVecVal.from_istring
  |> entype Type.const

let int64_max =
  Int64.max_int |> Int64.to_string |> BitVecVal.from_istring
  |> entype Type.const

let uint64_min = BitVecVal.from_int 0 |> entype Type.const

let uint64_max = BitVec.addi (BitVec.shli int64_max 1) 1

(* range check *)
let is_in_smi_range t = Bool.ands [ sge t smi_min; sle t smi_max ]

let is_empty value =
  let size = BitVec.length_of value / len in
  eq value (BitVec.repeat size empty)

module Int32 = struct
  type t = BitVec.t

  let from_value value =
    BitVec.andi (value |> data_of) Constants.smi_mask |> entype Type.int32

  let lt lval rval =
    let li = lval |> from_value in
    let ri = rval |> from_value in
    slt li ri

  let mul lval rval =
    let li = lval |> from_value in
    let ri = rval |> from_value in
    andi (mul li ri) Constants.smi_mask
end

module Int64 = struct
  type t = BitVec.t

  let lt lval rval = slt lval rval
end

module Float64 = struct
  type t = BitVec.t

  let lt lval rval =
    let lf = lval |> data_of |> Z3utils.Float.from_ieee_bv in
    let rf = rval |> data_of |> Z3utils.Float.from_ieee_bv in
    Z3utils.Float.lt lf rf
end

module Composed = struct
  type t = BitVec.t

  let init name size = BitVec.init ~len:(len * size) name

  let from_values values =
    List.fold_left
      (fun res value -> BitVec.concat res value)
      (List.hd values) (List.tl values)

  let size_of t = BitVec.length_of t / len

  let select idx t =
    let size = size_of t in
    BitVec.extract (((size - idx) * len) - 1) ((size - idx - 1) * len) t

  let first_of t = select 0 t

  let second_of t = select 1 t

  let to_list t =
    let size = size_of t in
    let rec aux res idx t =
      match idx with 0 -> res | _ -> aux (select idx t :: res) (idx - 1) t
    in
    t |> aux [] (size - 1)
end
