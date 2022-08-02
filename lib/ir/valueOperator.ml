open Z3utils

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

module TaggedPointer = struct
  type t = Value.t

  (* const *)
  (* 0-16: offset
     16-48: bid
     48-64: size of struct
     64-69: ty
  *)
  (* High |-ty-|-size-|--bid--|-offset-(1)-| Low *)
  let size_len = 32

  let bid_len = 16

  let off_len = 16

  let len = Value.ty_len + size_len + bid_len + off_len

  (* getter *)
  let size_of t =
    BitVec.extract (size_len + bid_len + off_len - 1) (bid_len + off_len) t

  let bid_of t = BitVec.extract (bid_len + off_len - 1) off_len t

  let to_raw_pointer t = BitVec.subi t 1 |> Value.data_of

  let off_of t = t |> to_raw_pointer |> BitVec.extract (off_len - 1) 0

  (* constructor *)
  let init bid sz =
    let bid = BitVecVal.from_int ~len:64 bid in
    let sz = Value.data_of sz in
    BitVec.ori
      (BitVec.orb
         (BitVec.shli sz (bid_len + off_len))
         (BitVec.shli bid off_len))
      1
    |> Value.entype Type.tagged_pointer

  (* method *)
  let next t = BitVec.addi t 1

  let move t pos = BitVec.addb t pos

  let movei t pos = BitVec.addi t pos

  let can_access pos sz t =
    (* no out-of-bounds *)
    let struct_size = Value.from_bv (size_of t) in
    let out_of_lb = BitVec.slti (pos |> Value.data_of) 0 in
    let out_of_ub =
      BitVec.ugtb
        (BitVec.addi pos sz |> Value.data_of)
        (struct_size |> Value.data_of)
    in
    Bool.not (Bool.ors [ out_of_lb; out_of_ub ])

  (* can read as [repr] *)
  let can_access_as pos repr t =
    let repr_sz = MachineType.Repr.size_of repr in
    can_access pos repr_sz t

  let to_string model t =
    let bid =
      let bid_str = bid_of t |> Model.eval model |> Expr.to_string in
      try
        "0" ^ String.sub bid_str 1 (String.length bid_str - 1)
        |> Int32.of_string |> Int32.unsigned_to_int |> Option.get
        |> string_of_int
      with _ -> bid_str
    in
    let offset =
      let off_str = off_of t |> Model.eval model |> Expr.to_string in
      try
        "0" ^ String.sub off_str 1 (String.length off_str - 1)
        |> Int32.of_string |> Int32.unsigned_to_int |> Option.get
        |> string_of_int
      with _ -> off_str
    in
    Format.sprintf "TaggedPointer(bid: %s, offset: %s)" bid offset
end

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

module Float64 = struct
  (* conversion *)
  let from_float f = f |> Float.to_ieee_bv |> Value.entype Type.float64

  let from_numeral f = f |> Float.from_float |> from_float

  let to_float value = value |> Value.data_of |> Float.from_ieee_bv

  let to_intx width value =
    let value_ix =
      let f = value |> to_float in
      let i_mod_2_x =
        Bool.ite (Float.is_negative f)
          (Integer.mod_
             (f |> Float.abs
             |> Float.to_sbv Float.rtn_mode
             |> BitVec.neg |> BitVec.to_sint)
             (Integer.from_int (Utils.pow 2 width)))
          (Integer.mod_
             (f |> Float.abs |> Float.to_sbv Float.rtn_mode |> BitVec.to_sint)
             (Integer.from_int (Utils.pow 2 width)))
      in
      Bool.ite
        (* if num is nan or 0 or -0 or inf or -inf, return 0 *)
        (Bool.ors
           [
             Float.is_nan f;
             Float.is_zero f;
             Float.is_minus_zero f;
             Float.is_inf f;
             Float.is_ninf f;
           ])
        (Integer.from_int 0)
        (* else *)
        (Bool.ite
           (Integer.ge i_mod_2_x (Integer.from_int (Utils.pow 2 (width - 1))))
           (Integer.sub i_mod_2_x (Integer.from_int (Utils.pow 2 width)))
           i_mod_2_x)
    in
    match width with
    | 32 ->
        value_ix |> Integer.to_bv ~len:32 |> BitVec.zero_extend 32
        |> Value.entype Type.int32
    | 64 -> value_ix |> Integer.to_bv ~len:64 |> Value.entype Type.int64
    | _ -> failwith "not implemented"

  let to_int32 value = value |> to_intx 32

  let to_int64 value = value |> to_intx 64

  let to_tagged_signed value = value |> to_int32 |> Int32.to_tagged_signed

  let to_uint32 value = value |> to_int32 |> Int32.to_int Type.uint32 32

  (* constants *)
  let nan = Float.nan () |> from_float

  let ninf = Float.ninf () |> from_float

  let inf = Float.inf () |> from_float

  let zero = Float.from_float 0.0 |> from_float

  let one = Float.from_float 1.0 |> from_float

  let minus_zero = Float.minus_zero () |> from_float

  let safe_integer_max = Float.safe_integer_max () |> from_float

  let safe_integer_min = Float.safe_integer_min () |> from_float

  (* arithmetic *)
  let abs value = Float.abs (value |> to_float) |> from_float

  let add lval rval =
    let lf = lval |> to_float in
    let rf = rval |> to_float in
    Float.add lf rf |> from_float

  let ceil value = Float.round Float.rtp_mode (value |> to_float) |> from_float

  let div lval rval =
    Float.div (lval |> to_float) (rval |> to_float) |> from_float

  let floor value = Float.round Float.rtn_mode (value |> to_float) |> from_float

  let mul lval rval =
    let lf = lval |> to_float in
    let rf = rval |> to_float in
    Float.mul lf rf |> from_float

  let neg value =
    let f = value |> to_float in
    Float.neg f |> from_float

  let rem lval rval =
    Float.rem (lval |> to_float) (rval |> to_float) |> from_float

  let trunc value = Float.round Float.rtz_mode (value |> to_float) |> from_float

  let round_down = floor

  let round_up = ceil

  let round_nearest_to_even value =
    Float.round Float.rne_mode (value |> to_float) |> from_float

  let sub lval rval =
    let lf = lval |> to_float in
    let rf = rval |> to_float in
    Float.sub lf rf |> from_float

  (* comparison *)
  let eq lval rval =
    let lf = lval |> to_float in
    let rf = rval |> to_float in
    Float.eq lf rf

  let le lval rval =
    let lf = lval |> to_float in
    let rf = rval |> to_float in
    Float.le lf rf

  let lt lval rval =
    let lf = lval |> to_float in
    let rf = rval |> to_float in
    Float.lt lf rf

  let ge lval rval =
    let lf = lval |> to_float in
    let rf = rval |> to_float in
    Float.ge lf rf

  let gt lval rval =
    let lf = lval |> to_float in
    let rf = rval |> to_float in
    Float.gt lf rf

  (* methods *)

  let is_integer value = eq value (value |> floor)

  let is_zero value = Float.is_zero (value |> to_float)

  let is_minus_zero value = Float.is_minus_zero (value |> to_float)

  let is_nan value = Float.is_nan (value |> to_float)

  let is_inf value = Float.is_inf (value |> to_float)

  let is_ninf value = Float.is_ninf (value |> to_float)

  let is_negative value =
    BitVec.eqi (BitVec.extract 63 63 (value |> Value.data_of)) 0

  let is_positive value =
    BitVec.eqi (BitVec.extract 63 63 (value |> Value.data_of)) 0

  let is_safe_integer value =
    Bool.ands
      [ is_integer value; ge value safe_integer_min; le value safe_integer_max ]

  let can_be_smi value =
    Bool.ands
      [
        value |> is_integer;
        Bool.not (value |> is_minus_zero);
        value |> to_int32 |> Int32.is_in_smi_range;
      ]

  let max lval rval =
    Float.max (lval |> to_float) (rval |> to_float) |> from_float

  let min lval rval =
    Float.min (lval |> to_float) (rval |> to_float) |> from_float

  let sin value =
    let bv_sort = BV.mk_sort ctx 64 in
    let uif = Z3.FuncDecl.mk_func_decl_s ctx "sin" [ bv_sort ] bv_sort in
    (* https://tc39.es/ecma262/#sec-math.sin *)
    Bool.ite
      (Bool.ors [ value |> is_nan; value |> is_zero; value |> is_minus_zero ])
      value
      (Bool.ite
         (Bool.ors [ value |> is_inf; value |> is_ninf ])
         nan
         (Z3.FuncDecl.apply uif [ value |> Value.data_of ]
         |> Value.entype Type.float64))

  (* pp *)
  let to_string model value =
    let evaluated = value |> Model.eval model in
    if String.contains (evaluated |> is_nan |> Expr.to_simplified_string) 't'
    then "Float64(NaN)"
    else if
      String.contains (evaluated |> is_inf |> Expr.to_simplified_string) 't'
    then "Float64(+oo)"
    else if
      String.contains (evaluated |> is_ninf |> Expr.to_simplified_string) 't'
    then "Float64(-oo)"
    else if
      String.contains
        (evaluated |> is_minus_zero |> Expr.to_simplified_string)
        't'
    then "Float64(-0.0)"
    else
      Format.sprintf "Float64(%s)"
        (evaluated |> to_float |> Model.eval model |> Real.to_decimal_string)
end
