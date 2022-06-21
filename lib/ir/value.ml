open Z3utils
module Repr = MachineType.Repr

type t = BitVec.t

(*  5-bit for type & 64-bit for data *)

let ty_len = Type.len

let data_len = 64

let len = ty_len + data_len

(* getter *)
let ty_of t = BitVec.extract (data_len + ty_len - 1) data_len t

let data_of t = BitVec.extract (data_len - 1) 0 t

(* cast value [t] to type [ty] *)
let cast ty t =
  if BitVec.length_of t <> len then (
    BitVec.length_of t |> string_of_int |> print_endline;
    failwith "invalid value length")
  else BitVec.concat ty (data_of t)

(* entype [data] to type [ty] *)
let entype ty data =
  let input_data_len = BitVec.length_of data in
  if input_data_len <> data_len then
    failwith (Printf.sprintf "invalid data length: %d" input_data_len)
    (* TODO handling undef of data *)
  else BitVec.concat ty data

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
let has_type (ty : Type.t) t =
  if ty = Type.any_tagged then
    Bool.ors
      [
        BitVec.eqb (ty_of t) Type.tagged_pointer;
        BitVec.eqb (ty_of t) Type.tagged_signed;
      ]
  else BitVec.eqb (ty_of t) ty

let is_signed_integer t =
  Bool.ors (List.map (fun ty -> has_type ty t) Type.int_types)

let is_unsigned_integer t =
  Bool.ors (List.map (fun ty -> has_type ty t) Type.uint_types)

let is_integer t = Bool.ors [ is_signed_integer t; is_unsigned_integer t ]

let is_float t = Bool.ors (List.map (fun ty -> has_type ty t) Type.float_types)

(* type casting operations *)

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

let ashri value i =
  let ty = ty_of value in
  BitVec.ashri (data_of value) i |> entype ty

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

let weak_eq ?(repr = Repr.Word64) lval rval =
  let width = Repr.width_of repr in
  BitVec.eqb
    (BitVec.extract (width - 1) 0 lval)
    (BitVec.extract (width - 1) 0 rval)

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

let abs ty value = value |> data_of |> BitVec.abs |> entype ty

(* Floating Point *)
let gef lval f =
  (* assmue that lval is integer or float *)
  let lval_f =
    Bool.ite (is_signed_integer lval)
      (Float.from_signed_bv (data_of lval))
      (Bool.ite (is_unsigned_integer lval)
         (Float.from_unsigned_bv (data_of lval))
         (Float.from_ieee_bv (data_of lval)))
  in
  Float.ge lval_f (Float.from_float f)

let lef lval f =
  (* assmue that lval is integer or float *)
  let lval_f =
    Bool.ite (is_signed_integer lval)
      (Float.from_signed_bv (data_of lval))
      (Bool.ite (is_unsigned_integer lval)
         (Float.from_unsigned_bv (data_of lval))
         (Float.from_ieee_bv (data_of lval)))
  in
  Float.le lval_f (Float.from_float f)

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

module Bool = struct
  let from_value value = value |> BitVec.extract 1 0

  let to_string model value =
    let v_str =
      value |> from_value |> Model.eval model |> Expr.to_simplified_string
    in
    Format.sprintf "Bool(0x%x)"
      ("0" ^ String.sub v_str 1 ((v_str |> String.length) - 1)
      |> Int32.of_string |> Int32.to_int)
end

module TaggedSigned = struct
  let from_value = BitVec.extract 31 1

  let to_value t = t |> BitVec.zero_extend 32 |> entype Type.tagged_signed

  let to_int32 value =
    value |> from_value |> BitVec.sign_extend 33 |> entype Type.int32

  let to_string model value =
    let v_str =
      value |> from_value |> Model.eval model |> Expr.to_simplified_string
    in
    Format.sprintf "TaggedSigned(0x%x)"
      ("0" ^ String.sub v_str 1 ((v_str |> String.length) - 1)
      |> Int32.of_string |> Int32.to_int)
end

module MapInHeader = struct
  let from_value value = value |> data_of |> Z3utils.BitVec.extract 31 0

  let to_string model value =
    let map_str = Objmap.to_string model (value |> from_value) in
    Format.sprintf "MapInHeader(%s)" map_str
end

module Int8 = struct
  let from_value value = BitVec.extract 7 0 value

  let to_value t = t |> BitVec.zero_extend 56 |> entype Type.int8

  let to_string model value =
    let v_str =
      value |> from_value |> Model.eval model |> BitVec.sign_extend 24
      |> Expr.to_simplified_string
    in
    Format.sprintf "Int8(0x%x)"
      ("0" ^ String.sub v_str 1 ((v_str |> String.length) - 1)
      |> Int32.of_string |> Int32.to_int)
end

module Int32 = struct
  let from_value value = BitVec.extract 31 0 value

  let to_value t = t |> BitVec.zero_extend 32 |> entype Type.int32

  let to_tagged_signed value =
    BitVec.shli (value |> from_value) 1
    |> BitVec.zero_extend 32 |> entype Type.tagged_signed

  let to_float64 value =
    value |> from_value |> BitVec.zero_extend 32 |> Float.from_signed_bv
    |> Float.to_ieee_bv |> entype Type.float64

  let to_string model value =
    let v_str =
      value |> from_value |> Model.eval model |> Expr.to_simplified_string
    in
    Format.sprintf "Int32(0x%x)"
      ("0" ^ String.sub v_str 1 ((v_str |> String.length) - 1)
      |> Int32.of_string |> Int32.to_int)

  let add lval rval =
    let li = lval |> from_value in
    let ri = rval |> from_value in
    BitVec.addb li ri |> to_value

  let mul lval rval =
    let li = lval |> from_value in
    let ri = rval |> from_value in
    BitVec.mulb li ri |> to_value

  let lt lval rval =
    let li = lval |> from_value in
    let ri = rval |> from_value in
    BitVec.sltb li ri |> to_value

  let is_in_smi_range value =
    Z3utils.Bool.ands
      [
        BitVec.sgei (value |> from_value) Constants.smi_min;
        BitVec.slei (value |> from_value) Constants.smi_max;
      ]
end

module Int64 = struct
  type t = BitVec.t

  let from_value value = BitVec.extract 63 0 value

  let to_value t = t |> entype Type.int64

  let to_tagged_signed value =
    BitVec.shli (BitVec.extract 31 0 value) 1
    |> BitVec.zero_extend 32 |> entype Type.tagged_signed

  let to_string model value =
    let v_str =
      value |> from_value |> Model.eval model |> Expr.to_simplified_string
    in
    Format.sprintf "Int64(0x%x)"
      ("0" ^ String.sub v_str 1 ((v_str |> String.length) - 1)
      |> Int64.of_string |> Int64.to_int)

  let lt lval rval = slt lval rval

  let is_in_smi_range value =
    Z3utils.Bool.ands
      [
        BitVec.sgei (value |> from_value) Constants.smi_min;
        BitVec.slei (value |> from_value) Constants.smi_max;
      ]
end

module Float64 = struct
  let from_value value = value |> data_of |> Z3utils.Float.from_ieee_bv

  let to_value t = t |> Z3utils.Float.to_ieee_bv |> entype Type.float64

  let to_int64 value =
    value |> from_value
    |> Float.to_sbv (Z3.FloatingPoint.RoundingMode.mk_round_toward_zero ctx)
    |> entype Type.int64

  let to_int32 value =
    andi (value |> to_int64) Constants.int32_mask |> cast Type.int32

  let to_string model value =
    let v_str =
      value |> from_value |> Model.eval model |> Real.to_decimal_string
    in
    Format.sprintf "Float64(%s)" v_str

  let is_minus_zero value = Float.is_minus_zero (value |> from_value)

  let eq lval rval =
    let lf = lval |> from_value in
    let rf = rval |> from_value in
    Z3utils.Float.eq lf rf

  let add lval rval =
    let lf = lval |> from_value in
    let rf = rval |> from_value in
    Z3utils.Float.add lf rf |> to_value

  let sub lval rval =
    let lf = lval |> from_value in
    let rf = rval |> from_value in
    Z3utils.Float.sub lf rf |> to_value

  let lt lval rval =
    let lf = lval |> from_value in
    let rf = rval |> from_value in
    Z3utils.Bool.ite (Z3utils.Float.lt lf rf) tr fl

  let le lval rval =
    let lf = lval |> from_value in
    let rf = rval |> from_value in
    Z3utils.Bool.ite (Z3utils.Float.le lf rf) tr fl
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
