open Z3utils

module type IntValue = sig
  val sign : bool

  val width : int

  val ty : Type.t
end

module Make_Integer_Operator (I : IntValue) = struct
  include I

  let from_value value = BitVec.extract (width - 1) 0 value

  let to_value t =
    t |> BitVec.zero_extend (Value.data_len - width) |> Value.entype ty

  (* arith *)
  let add lval rval =
    BitVec.addb (lval |> from_value) (rval |> from_value) |> to_value

  let sub lval rval =
    BitVec.subb (lval |> from_value) (rval |> from_value) |> to_value

  let mul lval rval =
    BitVec.mulb (lval |> from_value) (rval |> from_value) |> to_value

  let div lval rval =
    if sign then
      BitVec.sdivb (lval |> from_value) (rval |> from_value) |> to_value
    else BitVec.udivb (lval |> from_value) (rval |> from_value) |> to_value

  let modulo lval rval =
    BitVec.modb (lval |> from_value) (rval |> from_value) |> to_value

  (* assume turbofan consider 'overflow' as overflow \/ underflow *)
  let add_would_overflow lval rval =
    Z3utils.Bool.not
      (Z3utils.Bool.ands
         [
           BitVec.add_no_overflow lval rval sign;
           BitVec.add_no_underflow lval rval;
         ])

  let mul_would_overflow lval rval =
    Z3utils.Bool.not
      (Z3utils.Bool.ands
         [
           BitVec.mul_no_overflow lval rval sign;
           BitVec.mul_no_underflow lval rval;
         ])

  (* assume turbofan consider 'overflow' as overflow \/ underflow *)
  let sub_would_overflow lval rval =
    Z3utils.Bool.not
      (Z3utils.Bool.ands
         [
           BitVec.sub_no_overflow lval rval;
           BitVec.sub_no_underflow lval rval sign;
         ])

  (* bitwise *)
  let or_ lval rval =
    BitVec.orb (lval |> from_value) (rval |> from_value) |> to_value

  let lshr lval rval =
    BitVec.lshrb (lval |> from_value) (rval |> from_value) |> to_value

  (* comparison *)
  let eq lval rval = Z3utils.Bool.eq (lval |> from_value) (rval |> from_value)

  let lt lval rval =
    if sign then BitVec.sltb (lval |> from_value) (rval |> from_value)
    else BitVec.ultb (lval |> from_value) (rval |> from_value)

  let le lval rval =
    if sign then BitVec.sleb (lval |> from_value) (rval |> from_value)
    else BitVec.uleb (lval |> from_value) (rval |> from_value)

  let gt lval rval =
    if sign then BitVec.sgtb (lval |> from_value) (rval |> from_value)
    else BitVec.ugtb (lval |> from_value) (rval |> from_value)

  let ge lval rval =
    if sign then BitVec.sgeb (lval |> from_value) (rval |> from_value)
    else BitVec.ugeb (lval |> from_value) (rval |> from_value)

  (* conversion *)
  let to_int ty ty_width value =
    let data = value |> from_value in
    (if width < ty_width then
     if sign then BitVec.sign_extend (ty_width - width) data
     else BitVec.zero_extend (ty_width - width) data
    else BitVec.extract (ty_width - 1) 0 data)
    |> BitVec.zero_extend (Value.data_len - width)
    |> Value.entype ty

  let to_tagged_signed value =
    let data = value |> from_value in
    let extended =
      if sign then BitVec.sign_extend (32 - width) data
      else BitVec.zero_extend (32 - width) data
    in
    BitVec.shli extended 1 |> BitVec.zero_extend 32
    |> Value.entype Type.tagged_signed

  let to_float64 value =
    let data = value |> from_value in
    if sign then
      data |> Float.from_signed_bv |> Float.to_ieee_bv
      |> Value.entype Type.float64
    else
      data |> Float.from_unsigned_bv |> Float.to_ieee_bv
      |> Value.entype Type.float64

  (* constants *)
  let zero = BitVecVal.from_int ~len:width 0 |> to_value

  let min_limit =
    if sign then
      (* (1 << (width - 1)) *)
      BitVec.shli (BitVecVal.from_int ~len:width 1) (width - 1)
    else zero

  let max_limit =
    if sign then
      (* (1 << (width - 1)) - 1 *)
      BitVec.subi (BitVec.shli (BitVecVal.from_int ~len:width 1) (width - 1)) 1
    else
      (* (1 << width) - 1 *)
      BitVec.extract (width - 1) 0
        (BitVec.subi
           (BitVec.shli (BitVecVal.from_int ~len:(width + 1) 1) width)
           1)

  (* methods *)
  let is_negative value =
    if sign then BitVec.slti (value |> from_value) 0 else Bool.fl

  let is_positive value =
    if sign then BitVec.sgti (value |> from_value) 0 else Bool.tr

  let is_zero value = BitVec.eqi (value |> from_value) 0

  let is_in_smi_range value =
    if sign then
      Z3utils.Bool.ands
        [
          BitVec.sgei (value |> from_value) Constants.smi_min;
          BitVec.slei (value |> from_value) Constants.smi_max;
        ]
    else
      Z3utils.Bool.ands
        [
          BitVec.ugei (value |> from_value) 0;
          BitVec.ulei (value |> from_value) Constants.smi_max;
        ]

  (* pp *)
  let to_string model value =
    let v_str =
      value |> from_value |> Model.eval model |> Expr.to_simplified_string
    in
    try
      if sign then
        Format.sprintf "%s(%d)"
          (ty |> Type.to_string model)
          ("0" ^ String.sub v_str 1 ((v_str |> String.length) - 1)
          |> Int32.of_string |> Int32.to_int)
      else
        Format.sprintf "%s(0x%Lx)"
          (ty |> Type.to_string model)
          ("0" ^ String.sub v_str 1 ((v_str |> String.length) - 1)
          |> Int64.of_string)
    with _ -> v_str
end

module TaggedSigned = struct
  let from_value = BitVec.extract 31 1

  let to_value t =
    BitVec.concat t (BitVecVal.from_int ~len:1 0)
    |> BitVec.zero_extend 32
    |> Value.entype Type.tagged_signed

  let to_int32 value =
    value |> from_value |> BitVec.sign_extend 1 |> BitVec.zero_extend 32
    |> Value.entype Type.int32

  let to_int64 value =
    value |> from_value |> BitVec.sign_extend 33 |> Value.entype Type.int64

  let to_float64 value =
    value |> from_value |> Float.from_signed_bv |> Float.to_ieee_bv
    |> Value.entype Type.float64

  let to_uint32 value = value |> to_int32 |> Value.cast Type.uint32

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
      (Value.cast Type.tagged_signed value)
      (Value.cast Type.tagged_pointer value)
end

module Boolean = struct
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
  let from_value value = value |> Value.data_of |> Z3utils.BitVec.extract 31 0

  let to_string model value =
    let map_str = Objmap.to_string model (value |> from_value) in
    Format.sprintf "MapInHeader(%s)" map_str
end

module Int8 = Make_Integer_Operator (struct
  let sign = false

  let width = 8

  let ty = Type.int8
end)

module Int32 = Make_Integer_Operator (struct
  let sign = true

  let width = 32

  let ty = Type.int32
end)

module Int64 = Make_Integer_Operator (struct
  let sign = true

  let width = 32

  let ty = Type.int32
end)

module Uint32 = Make_Integer_Operator (struct
  let sign = false

  let width = 32

  let ty = Type.uint32
end)

module Uint64 = Make_Integer_Operator (struct
  let sign = false

  let width = 32

  let ty = Type.uint64
end)

module Composed = struct
  type t = BitVec.t

  let init name size = BitVec.init ~len:(Value.len * size) name

  let from_values values =
    List.fold_left
      (fun res value -> BitVec.concat res value)
      (List.hd values) (List.tl values)

  let size_of t = BitVec.length_of t / Value.len

  let select idx t =
    let size = size_of t in
    BitVec.extract
      (((size - idx) * Value.len) - 1)
      ((size - idx - 1) * Value.len)
      t

  let first_of t = select 0 t

  let second_of t = select 1 t

  let to_list t =
    let size = size_of t in
    let rec aux res idx t =
      match idx with 0 -> res | _ -> aux (select idx t :: res) (idx - 1) t
    in
    t |> aux [] (size - 1)
end

module type WordValue = sig
  val repr : MachineType.Repr.t
end

module Make_Word_Operator (W : WordValue) = struct
  open MachineType

  let width = Repr.width_of W.repr

  (* choose arbitrary one *)
  let ty = W.repr |> Type.from_repr |> List.hd

  let from_value value = BitVec.extract (width - 1) 0 value

  let to_value data =
    BitVec.zero_extend (Value.data_len - width) data |> Value.entype ty

  let eq lval rval = Z3utils.Bool.eq (lval |> from_value) (rval |> from_value)

  (* bitwise *)
  let and_ lval rval =
    BitVec.andb (lval |> from_value) (rval |> from_value) |> to_value

  let or_ lval rval =
    BitVec.orb (lval |> from_value) (rval |> from_value) |> to_value

  let xor lval rval =
    BitVec.xor (lval |> from_value) (rval |> from_value) |> to_value

  let shl lval rval =
    BitVec.shlb (lval |> from_value) (rval |> from_value) |> to_value

  let ashr lval rval =
    BitVec.ashrb (lval |> from_value) (rval |> from_value) |> to_value

  let lshr lval rval =
    BitVec.lshrb (lval |> from_value) (rval |> from_value) |> to_value

  let swap value =
    if width = 32 then BitVec.swap32 (value |> from_value) |> to_value
    else if width = 64 then BitVec.swap64 (value |> from_value) |> to_value
    else failwith "not supported"

  (* methods *)
  let mask lval rval =
    BitVec.modb (lval |> from_value)
      (BitVec.shlb (BitVecVal.from_int ~len:width 1) (rval |> from_value))
end

module Word8 = Make_Word_Operator (struct
  let repr = MachineType.Repr.Word8
end)

module Word16 = Make_Word_Operator (struct
  let repr = MachineType.Repr.Word8
end)

module Word32 = Make_Word_Operator (struct
  let repr = MachineType.Repr.Word8
end)

module Word64 = Make_Word_Operator (struct
  let repr = MachineType.Repr.Word8
end)