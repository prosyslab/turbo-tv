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

let from_f64string s = BitVecVal.from_f64string s |> entype Type.const

let from_bv bv =
  BitVec.zero_extend (len - BitVec.length_of bv) bv |> cast Type.const

let empty = from_int 0 |> cast Type.empty

(* type checks *)
let rec has_type (ty : Type.t) t =
  if ty = Type.any_tagged then
    Bool.ors
      [ t |> has_type Type.tagged_pointer; t |> has_type Type.tagged_signed ]
  else if ty = Type.tagged_signed then
    Bool.ands [ BitVec.eqb (ty_of t) ty; BitVec.eqi (BitVec.andi t 1) 0 ]
  else if ty = Type.tagged_pointer then
    Bool.ands [ BitVec.eqb (ty_of t) ty; BitVec.eqi (BitVec.andi t 1) 1 ]
  else BitVec.eqb (ty_of t) ty

let have_type t ts = Bool.ands (List.map (has_type t) ts)

let is_signed_integer t =
  Bool.ors (List.map (fun ty -> has_type ty t) Type.int_types)

let is_unsigned_integer t =
  Bool.ors (List.map (fun ty -> has_type ty t) Type.uint_types)

let is_integer t = Bool.ors [ is_signed_integer t; is_unsigned_integer t ]

let is_float t = Bool.ors (List.map (fun ty -> has_type ty t) Type.float_types)

(* type casting operations *)

let uint32_to_int64 t = t |> cast Type.int64

let int64_to_float64 t =
  data_of t |> Float.from_signed_bv |> Float.to_ieee_bv |> entype Type.float64

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

let swap32 value =
  let ty = ty_of value in
  BitVec.swap32 (data_of value) |> entype ty

let swap64 value =
  let ty = ty_of value in
  BitVec.swap64 (data_of value) |> entype ty

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

let ltf lval rval =
  let lf = lval |> data_of |> Float.from_ieee_bv in
  let rf = rval |> data_of |> Float.from_ieee_bv in
  Float.lt lf rf

(* constant values *)

let fl = empty |> cast Type.bool

let is_false value = eq fl value

let tr = addi empty 1 |> cast Type.bool

let is_true value = eq tr value

let to_bool value = Bool.ite (eq value fl) Bool.fl Bool.tr

let zero = BitVecVal.zero () |> entype Type.const

let undefined = empty |> cast Type.undefined

let is_undefined value = eq undefined value

(* IEEE-754 *)
let inf = BitVecVal.inf () |> entype Type.float64

let ninf = BitVecVal.ninf () |> entype Type.float64

let minus_zero = BitVecVal.minus_zero () |> entype Type.float64

let nan = BitVecVal.nan () |> entype Type.float64

(* smi constant values *)
let smi_min = Constants.smi_min |> BitVecVal.from_int |> entype Type.const

let smi_max = Constants.smi_max |> BitVecVal.from_int |> entype Type.const

(* Int64 constant values *)
let int64_min =
  Int64.min_int |> Int64.to_string |> BitVecVal.from_istring
  |> entype Type.const

let int64_max =
  Int64.max_int |> Int64.to_string |> BitVecVal.from_istring
  |> entype Type.const

let uint64_min = BitVecVal.from_int 0 |> entype Type.const

let uint64_max = BitVec.addi (BitVec.shli int64_max 1) 1

module TaggedSigned = struct
  let from_value = BitVec.extract 31 1

  let to_value t =
    BitVec.concat t (BitVecVal.from_int ~len:1 0)
    |> BitVec.zero_extend 32 |> entype Type.tagged_signed

  let to_int32 value =
    value |> from_value |> BitVec.sign_extend 1 |> BitVec.zero_extend 32
    |> entype Type.int32

  let to_int64 value =
    value |> from_value |> BitVec.sign_extend 33 |> entype Type.int64

  let to_float64 value =
    value |> from_value |> Float.from_signed_bv |> Float.to_ieee_bv
    |> entype Type.float64

  let to_uint32 value = value |> to_int32 |> cast Type.uint32

  let is_zero value =
    BitVec.eqb (value |> from_value) (BitVecVal.zero ~len:31 ())

  let to_string model value =
    let v_str =
      value |> from_value |> BitVec.sign_extend 1 |> Model.eval model
      |> Expr.to_simplified_string
    in
    Format.sprintf "TaggedSigned(%d)"
      ("0" ^ String.sub v_str 1 ((v_str |> String.length) - 1)
      |> Int32.of_string |> Int32.to_int)
end

module AnyTagged = struct
  let settle value =
    let is_tagged_signed value =
      Bool.eq (BitVec.extract 0 0 value) (BitVecVal.from_int ~len:1 0)
    in
    Bool.ite (is_tagged_signed value)
      (cast Type.tagged_signed value)
      (cast Type.tagged_pointer value)
end

module Bool = struct
  let from_value value = value |> BitVec.extract 1 0

  let to_string model value =
    let v_str =
      value |> from_value |> Model.eval model |> Expr.to_simplified_string
    in
    try
      Format.sprintf "Bool(0x%x)"
        ("0" ^ String.sub v_str 1 ((v_str |> String.length) - 1)
        |> Int32.of_string |> Int32.to_int)
    with _ -> v_str
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

  let str_to_value s = BitVecVal.from_istring ~len:32 s |> to_value

  (* type-conversion *)
  let to_float64 value =
    value |> from_value |> BitVec.sign_extend 32 |> Float.from_signed_bv
    |> Float.to_ieee_bv |> entype Type.float64

  let to_int64 value =
    value |> from_value |> BitVec.sign_extend 32 |> entype Type.int64

  let to_tagged_signed value =
    BitVec.shli (value |> from_value) 1
    |> BitVec.zero_extend 32 |> entype Type.tagged_signed

  let to_uint32 value = value |> cast Type.uint32

  (* Int32 V x Int32 V *)
  let add lval rval =
    let li = lval |> from_value in
    let ri = rval |> from_value in
    BitVec.addb li ri |> to_value

  let mul lval rval =
    let li = lval |> from_value in
    let ri = rval |> from_value in
    BitVec.mulb li ri |> to_value

  let sub lval rval =
    BitVec.subb (lval |> from_value) (rval |> from_value) |> to_value

  let or_ lval rval =
    let li = lval |> from_value in
    let ri = rval |> from_value in
    BitVec.orb li ri |> to_value

  let lt lval rval =
    let li = lval |> from_value in
    let ri = rval |> from_value in
    BitVec.sltb li ri

  let le lval rval =
    let li = lval |> from_value in
    let ri = rval |> from_value in
    BitVec.sleb li ri

  let ge lval rval =
    let li = lval |> from_value in
    let ri = rval |> from_value in
    BitVec.sgeb li ri

  (* constant *)
  let min_value =
    BitVecVal.from_int ~len:32 (Int32.min_int |> Int32.to_int) |> to_value

  let max_value =
    BitVecVal.from_int ~len:32 (Int32.max_int |> Int32.to_int) |> to_value

  (* method *)
  let is_in_smi_range value =
    Z3utils.Bool.ands
      [
        BitVec.sgei (value |> from_value) Constants.smi_min;
        BitVec.slei (value |> from_value) Constants.smi_max;
      ]

  (* pp *)
  let to_string model value =
    let v_str =
      value |> from_value |> Model.eval model |> Expr.to_simplified_string
    in
    try
      Format.sprintf "Int32(%d)"
        ("0" ^ String.sub v_str 1 ((v_str |> String.length) - 1)
        |> Int32.of_string |> Int32.to_int)
    with _ -> v_str
end

module Uint32 = struct
  type t = BitVec.t

  let from_value value = BitVec.extract 31 0 value

  (* conversion *)
  let to_value t = t |> BitVec.zero_extend 32 |> entype Type.uint32

  let to_float64 value =
    value |> from_value |> Float.from_unsigned_bv |> Float.to_ieee_bv
    |> entype Type.float64

  let to_int32 value = value |> cast Type.int32

  let to_tagged_signed value =
    BitVec.shli (value |> from_value) 1
    |> BitVec.zero_extend 32 |> entype Type.tagged_signed

  (* arith *)
  let modulo lval rval =
    BitVec.modb (lval |> from_value) (rval |> from_value) |> to_value

  let mul lval rval =
    BitVec.mulb (lval |> from_value) (rval |> from_value) |> to_value

  (* bitwise *)
  let lshr lval rval =
    BitVec.lshrb (lval |> from_value) (rval |> from_value) |> to_value

  (* method *)
  let is_in_smi_range value =
    BitVec.ulei (value |> from_value) Constants.smi_max

  (* pp *)
  let to_string model value =
    let v_str =
      value |> from_value |> Model.eval model |> Expr.to_simplified_string
    in
    Format.sprintf "Uint32(0x%x)"
      ("0" ^ String.sub v_str 1 ((v_str |> String.length) - 1) |> int_of_string)
end

module Uint64 = struct
  type t = BitVec.t

  let from_value value = BitVec.extract 63 0 value

  (* conversion *)
  let to_value t = t |> entype Type.uint64

  let to_float64 value =
    value |> from_value |> Float.from_unsigned_bv |> Float.to_ieee_bv
    |> entype Type.float64

  let to_tagged_signed value =
    BitVec.shli (BitVec.extract 31 0 value) 1
    |> BitVec.zero_extend 32 |> entype Type.tagged_signed

  (* method *)
  let is_in_smi_range value =
    BitVec.ulei (value |> from_value) Constants.smi_max

  (* pp *)
  let to_string model value =
    let v_str =
      value |> from_value |> Model.eval model |> Expr.to_simplified_string
    in
    Format.sprintf "Uint64(0x%Lx)"
      ("0" ^ String.sub v_str 1 ((v_str |> String.length) - 1)
      |> Int64.of_string)
end

module Int64 = struct
  type t = BitVec.t

  let from_value value = BitVec.extract 63 0 value

  let to_value t = t |> entype Type.int64

  let str_to_value s = BitVecVal.from_istring s |> to_value

  (* conversion *)
  let to_float64 value =
    value |> from_value |> Float.from_signed_bv |> Float.to_ieee_bv
    |> entype Type.float64

  let to_int32 value =
    value |> from_value |> BitVec.extract 31 0 |> BitVec.zero_extend 32
    |> entype Type.int32

  let to_tagged_signed value =
    BitVec.shli (BitVec.extract 31 0 value) 1
    |> BitVec.zero_extend 32 |> entype Type.tagged_signed

  let is_in_smi_range value =
    Z3utils.Bool.ands
      [
        BitVec.sgei (value |> from_value) Constants.smi_min;
        BitVec.slei (value |> from_value) Constants.smi_max;
      ]

  let lt lval rval = slt lval rval

  let add lval rval = add lval rval |> cast Type.int64

  let sub lval rval = sub lval rval |> cast Type.int64

  (* pp *)
  let to_string model value =
    let v_str =
      value |> from_value |> Model.eval model |> Expr.to_simplified_string
    in
    try
      Format.sprintf "Int64(0x%Lx)"
        ("0" ^ String.sub v_str 1 ((v_str |> String.length) - 1)
        |> Int64.of_string)
    with _ -> v_str
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
