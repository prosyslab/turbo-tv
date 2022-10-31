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

  let is_in_range value lb ub =
    Bool.ands
      [
        BitVec.sgei (value |> from_value) lb;
        BitVec.slei (value |> from_value) ub;
      ]

  let eq lval rval = BitVec.eqb (lval |> from_value) (rval |> from_value)

  let to_string model value =
    let v_str =
      value |> from_value |> BitVec.sign_extend 1 |> Model.eval model
      |> Expr.to_simplified_string
    in
    Format.sprintf "TaggedSigned(%d)"
      ("0" ^ String.sub v_str 1 ((v_str |> String.length) - 1)
      |> Int32.of_string |> Int32.to_int)

  let min_limit = -1073741824

  let max_limit = 1073741823
end

module TaggedPointer = struct
  type t = Value.t

  (* const *)
  (* 0-32: offset
     32-64: bid
     64-69: ty
  *)
  (* High |-ty-|---offset-1--|---bid---| Low *)

  let bid_len = 32

  let off_len = 32

  let len = Value.ty_len + bid_len + off_len

  (* getter *)

  let bid_of t = BitVec.extract (bid_len + off_len - 1) off_len t

  let to_raw_pointer t = BitVec.subi t 1 |> Value.data_of

  let off_of t = t |> to_raw_pointer |> BitVec.extract (off_len - 1) 0

  (* constructor *)
  let init bid =
    BitVec.ori
      (BitVec.shli
         (bid |> BitVec.zero_extend (Value.data_len - bid_len))
         off_len)
      1
    |> Value.entype Type.tagged_pointer

  (* method *)
  let next t = BitVec.addi t 1

  let move t pos = BitVec.addb t pos

  let movei t pos = BitVec.addi t pos

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

  let of_int i = BitVecVal.from_int ~len:width i |> to_value

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

  let srem lval rval =
    BitVec.sremb (lval |> from_value) (rval |> from_value) |> to_value

  let urem lval rval =
    BitVec.uremb (lval |> from_value) (rval |> from_value) |> to_value

  let modulo = if sign then srem else urem

  (* assume turbofan consider 'overflow' as overflow \/ underflow *)
  let add_would_overflow lval rval =
    let lval = lval |> from_value in
    let rval = rval |> from_value in
    Z3utils.Bool.not
      (Z3utils.Bool.ands
         [
           BitVec.add_no_overflow lval rval sign;
           BitVec.add_no_underflow lval rval;
         ])

  let mul_would_overflow lval rval =
    let lval = lval |> from_value in
    let rval = rval |> from_value in
    Z3utils.Bool.not
      (Z3utils.Bool.ands
         [
           BitVec.mul_no_overflow lval rval sign;
           BitVec.mul_no_underflow lval rval;
         ])

  (* assume turbofan consider 'overflow' as overflow \/ underflow *)
  let sub_would_overflow lval rval =
    let lval = lval |> from_value in
    let rval = rval |> from_value in
    Z3utils.Bool.not
      (Z3utils.Bool.ands
         [
           BitVec.sub_no_overflow lval rval;
           BitVec.sub_no_underflow lval rval sign;
         ])

  (* bitwise *)
  let or_ lval rval =
    BitVec.orb (lval |> from_value) (rval |> from_value) |> to_value

  let shl lval rval =
    BitVec.shlb (lval |> from_value) (rval |> from_value) |> to_value

  let lshr lval rval =
    BitVec.lshrb (lval |> from_value) (rval |> from_value) |> to_value

  let ashr lval rval =
    BitVec.ashrb (lval |> from_value) (rval |> from_value) |> to_value

  (* comparison *)
  let eq lval rval = Z3utils.Bool.eq (lval |> from_value) (rval |> from_value)

  let lt lval rval =
    if sign then BitVec.sltb (lval |> from_value) (rval |> from_value)
    else BitVec.ultb (lval |> from_value) (rval |> from_value)

  let le lval rval =
    if sign then BitVec.sleb (lval |> from_value) (rval |> from_value)
    else BitVec.uleb (lval |> from_value) (rval |> from_value)

  let lei lval n =
    if sign then BitVec.slei (lval |> from_value) n
    else BitVec.ulei (lval |> from_value) n

  let gt lval rval =
    if sign then BitVec.sgtb (lval |> from_value) (rval |> from_value)
    else BitVec.ugtb (lval |> from_value) (rval |> from_value)

  let ge lval rval =
    if sign then BitVec.sgeb (lval |> from_value) (rval |> from_value)
    else BitVec.ugeb (lval |> from_value) (rval |> from_value)

  let gei lval n =
    if sign then BitVec.sgei (lval |> from_value) n
    else BitVec.ugei (lval |> from_value) n

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
          BitVec.sgei (value |> from_value) TaggedSigned.min_limit;
          BitVec.slei (value |> from_value) TaggedSigned.max_limit;
        ]
    else
      Z3utils.Bool.ands
        [
          BitVec.ugei (value |> from_value) 0;
          BitVec.ulei (value |> from_value) TaggedSigned.max_limit;
        ]

  let min lval rval =
    if sign then
      Bool.ite (BitVec.sltb (lval |> from_value) (rval |> from_value)) lval rval
    else
      Bool.ite (BitVec.ultb (lval |> from_value) (rval |> from_value)) lval rval

  let max lval rval =
    if sign then
      Bool.ite (BitVec.sgtb (lval |> from_value) (rval |> from_value)) lval rval
    else
      Bool.ite (BitVec.ugtb (lval |> from_value) (rval |> from_value)) lval rval

  let is_in_range value lb ub =
    let lb_v = lb |> Value.from_int |> Value.cast ty in
    let ub_v = ub |> Value.from_int |> Value.cast ty in
    let lb = min lb_v ub_v in
    let ub = max lb_v ub_v in
    Z3utils.Bool.ands [ ge value lb; le value ub ]

  (* conversion *)
  let to_int ty ty_width value =
    let data = value |> from_value in
    let converted =
      if width < ty_width then
        if sign then BitVec.sign_extend (ty_width - width) data
        else BitVec.zero_extend (ty_width - width) data
      else BitVec.extract (ty_width - 1) 0 data
    in
    converted
    |> (fun converted ->
         if Value.data_len > ty_width then
           converted |> BitVec.zero_extend (Value.data_len - ty_width)
         else converted)
    |> Value.entype ty

  let to_tagged_signed value =
    let data = value |> from_value in
    let extended =
      if width < 32 then
        if sign then BitVec.sign_extend (32 - width) data
        else BitVec.zero_extend (32 - width) data
      else BitVec.extract (32 - 1) 0 data
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
  let sign = true

  let width = 8

  let ty = Type.int8
end)

module Uint8 = Make_Integer_Operator (struct
  let sign = false

  let width = 8

  let ty = Type.uint8
end)

module Int32 = Make_Integer_Operator (struct
  let sign = true

  let width = 32

  let ty = Type.int32
end)

module Int64 = Make_Integer_Operator (struct
  let sign = true

  let width = 64

  let ty = Type.int64
end)

module Uint32 = Make_Integer_Operator (struct
  let sign = false

  let width = 32

  let ty = Type.uint32
end)

module Uint64 = Make_Integer_Operator (struct
  let sign = false

  let width = 64

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

  let eq lval rval =
    if width = 32 then
      Bool.ite
        (Bool.ands
           [
             lval |> Value.has_type Type.tagged_pointer;
             rval |> Value.has_type Type.tagged_pointer;
           ])
        (BitVec.eqb
           (lval |> TaggedPointer.bid_of)
           (rval |> TaggedPointer.bid_of))
        (Bool.ite
           (Bool.ors
              [
                lval |> Value.has_type Type.tagged_pointer;
                rval |> Value.has_type Type.tagged_pointer;
              ])
           Bool.fl
           (Z3utils.Bool.eq (lval |> from_value) (rval |> from_value)))
    else Z3utils.Bool.eq (lval |> from_value) (rval |> from_value)

  let eqi lval ri = BitVec.eqi (lval |> from_value) ri

  (* bitwise *)
  let and_ lval rval =
    BitVec.andb (lval |> from_value) (rval |> from_value) |> to_value

  let andi lval ri = BitVec.andi (lval |> from_value) ri |> to_value

  let or_ lval rval =
    BitVec.orb (lval |> from_value) (rval |> from_value) |> to_value

  let xor lval rval =
    BitVec.xor (lval |> from_value) (rval |> from_value) |> to_value

  let rol lval rval =
    BitVec.rolb (lval |> from_value) (andi rval (width - 1) |> from_value)
    |> to_value

  let ror lval rval =
    BitVec.rorb (lval |> from_value) (andi rval (width - 1) |> from_value)
    |> to_value

  let shl lval rval =
    BitVec.shlb (lval |> from_value) (andi rval (width - 1) |> from_value)
    |> to_value

  let ashr lval rval =
    BitVec.ashrb (lval |> from_value) (andi rval (width - 1) |> from_value)
    |> to_value

  let lshr lval rval =
    BitVec.lshrb (lval |> from_value) (andi rval (width - 1) |> from_value)
    |> to_value

  let swap value =
    if width = 32 then BitVec.swap32 (value |> from_value) |> to_value
    else if width = 64 then BitVec.swap64 (value |> from_value) |> to_value
    else failwith "not supported"

  (* methods *)
  let mask lval rval =
    BitVec.modb (lval |> from_value)
      (BitVec.shlb (BitVecVal.from_int ~len:width 1) (rval |> from_value))
    |> to_value
end

module Word8 = Make_Word_Operator (struct
  let repr = MachineType.Repr.Word8
end)

module Word16 = Make_Word_Operator (struct
  let repr = MachineType.Repr.Word16
end)

module Word32 = Make_Word_Operator (struct
  let repr = MachineType.Repr.Word32
end)

module Word64 = Make_Word_Operator (struct
  let repr = MachineType.Repr.Word64
end)

module Float64 = struct
  (* conversion *)
  let to_value f = f |> Float.to_ieee_bv |> Value.entype Type.float64

  let of_float f = f |> Float.from_float |> to_value

  let from_value value = value |> Value.data_of |> Float.from_ieee_bv

  (* constants *)
  let nan = Float.nan () |> to_value

  let ninf = Float.ninf () |> to_value

  let inf = Float.inf () |> to_value

  let zero = Float.from_float 0.0 |> to_value

  let one = Float.from_float 1.0 |> to_value

  let minus_zero = Float.minus_zero () |> to_value

  let safe_integer_max = Float.safe_integer_max () |> to_value

  let safe_integer_min = Float.safe_integer_min () |> to_value

  (* arithmetic *)
  let abs value = Float.abs (value |> from_value) |> to_value

  let add lval rval =
    let lf = lval |> from_value in
    let rf = rval |> from_value in
    Float.add lf rf |> to_value

  let sub lval rval =
    let lf = lval |> from_value in
    let rf = rval |> from_value in
    Float.sub lf rf |> to_value

  let ceil value = Float.round Float.rtp_mode (value |> from_value) |> to_value

  let div lval rval =
    Float.div (lval |> from_value) (rval |> from_value) |> to_value

  let floor value = Float.round Float.rtn_mode (value |> from_value) |> to_value

  let mul lval rval =
    let lf = lval |> from_value in
    let rf = rval |> from_value in
    Float.mul lf rf |> to_value

  let neg value =
    let f = value |> from_value in
    Float.neg f |> to_value

  let trunc value = Float.round Float.rtz_mode (value |> from_value) |> to_value

  let round_down = floor

  let round_up = ceil

  let round_nearest_to_even value =
    Float.round Float.rne_mode (value |> from_value) |> to_value

  (* comparison *)
  let eq lval rval =
    let lf = lval |> from_value in
    let rf = rval |> from_value in
    Float.eq lf rf

  let le lval rval =
    let lf = lval |> from_value in
    let rf = rval |> from_value in
    Float.le lf rf

  let lt lval rval =
    let lf = lval |> from_value in
    let rf = rval |> from_value in
    Float.lt lf rf

  let ge lval rval =
    let lf = lval |> from_value in
    let rf = rval |> from_value in
    Float.ge lf rf

  let gt lval rval =
    let lf = lval |> from_value in
    let rf = rval |> from_value in
    Float.gt lf rf

  (* methods *)

  let is_zero value = Float.is_zero (value |> from_value)

  let is_minus_zero value = Float.is_minus_zero (value |> from_value)

  let is_nan value = Float.is_nan (value |> from_value)

  let is_inf value = Float.is_pinf (value |> from_value)

  let is_ninf value = Float.is_ninf (value |> from_value)

  let is_negative value =
    BitVec.eqi (BitVec.extract 63 63 (value |> Value.data_of)) 1

  let is_positive value =
    BitVec.eqi (BitVec.extract 63 63 (value |> Value.data_of)) 0

  let is_integer value =
    Bool.ite
      (Bool.ors [ value |> is_inf; value |> is_ninf; value |> is_nan ])
      Bool.fl
      (eq value (value |> floor))

  let is_safe_integer value =
    Bool.ands
      [ is_integer value; ge value safe_integer_min; le value safe_integer_max ]

  let is_in_smi_range value =
    Bool.ands
      [
        ge value (of_float (TaggedSigned.min_limit |> float_of_int));
        le value (of_float (TaggedSigned.max_limit |> float_of_int));
      ]

  let is_in_range value lb ub =
    Bool.ands [ ge value (of_float lb); le value (of_float ub) ]

  let can_be_smi value =
    Bool.ands [ value |> is_integer; value |> is_in_smi_range ]

  let max lval rval =
    (* UCOMISD: https://www.felixcloutier.com/x86/ucomisd *)
    Bool.ite
      (* nan, nan -> nan *)
      (Bool.ors [ lval |> is_nan; rval |> is_nan ])
      nan
      (Bool.ite
         (* -0, 0 -> 0 *)
         (Bool.ands [ lval |> is_minus_zero; rval |> is_zero ])
         zero
         (Bool.ite
            (* 0, -0 -> 0 *)
            (Bool.ands [ lval |> is_zero; rval |> is_minus_zero ])
            zero
            (* n1, n2 -> n1 > n2 ? n1 : n2 *)
            (Bool.ite (gt lval rval) lval rval)))

  let min lval rval =
    (* UCOMISD: https://www.felixcloutier.com/x86/ucomisd *)
    Bool.ite
      (* nan, nan -> nan *)
      (Bool.ors [ lval |> is_nan; rval |> is_nan ])
      nan
      (Bool.ite
         (* -0, 0 -> -0 *)
         (Bool.ands [ lval |> is_minus_zero; rval |> is_zero ])
         minus_zero
         (Bool.ite
            (* 0, -0 -> -0 *)
            (Bool.ands [ lval |> is_zero; rval |> is_minus_zero ])
            minus_zero
            (* n1, n2 -> n1 < n2 ? n1 : n2 *)
            (Bool.ite (lt lval rval) lval rval)))

  let expm1 value =
    let float_sort = Z3utils.Float.double_sort in
    let expm_decl =
      Z3.FuncDecl.mk_func_decl_s ctx "float64_expm1" [ float_sort ] float_sort
    in
    (* if num is NaN or 0 or -0 or inf, return num*)
    Bool.ite
      (Bool.ors
         [ is_nan value; is_zero value; is_minus_zero value; is_inf value ])
      value
      (* if num is -inf, return -1 *)
      (Bool.ite (is_ninf value) (of_float (-1.0))
         (Z3.FuncDecl.apply expm_decl [ value |> from_value ] |> to_value))

  let sin value =
    let float_sort = Z3utils.Float.double_sort in
    let uif =
      Z3.FuncDecl.mk_func_decl_s ctx "float64_sin" [ float_sort ] float_sort
    in
    (* https://tc39.es/ecma262/#sec-math.sin *)
    Bool.ite
      (Bool.ors [ value |> is_nan; value |> is_zero; value |> is_minus_zero ])
      value
      (Bool.ite
         (Bool.ors [ value |> is_inf; value |> is_ninf ])
         nan
         (Z3.FuncDecl.apply uif [ value |> from_value ] |> to_value))

  let to_intx ?(sign = true) width value =
    (* https://tc39.es/ecma262/#sec-toint32 *)
    let value_w_bit =
      let modulo =
        Stdlib.Float.pow 2.0 (width |> float_of_int) |> Float.from_float
      in
      let f = value |> from_value in
      let number =
        Bool.ite
          (* Note: http://smtlib.cs.uiowa.edu/theories-FloatingPoint.shtml
              fp.to_* functions are unspecified for NaN and infinity input values.
              In addition, fp.to_ubv and fp.to_sbv are unspecified for finite number inputs
              that are out of range (which includes all negative numbers for fp.to_ubv). *)
          (* if num is nan or 0 or -0 or inf or -inf, return 0 *)
          (Bool.ors
             [
               Float.is_nan f;
               Float.is_zero f;
               Float.is_minus_zero f;
               Float.is_inf f;
               Float.is_ninf f;
             ])
          (Float.from_float 0.0) f
      in
      let i =
        let fan = number |> Float.abs |> Float.round Float.rtn_mode in
        Bool.ite (Float.is_positive f) fan (Float.neg fan)
      in
      let remainder = Float.rem i modulo in
      Bool.ite
        (Float.is_positive remainder)
        (remainder |> Float.to_ubv ~len:width Float.rne_mode)
        (remainder |> Float.to_sbv ~len:width Float.rne_mode)
    in

    match width with
    | 32 ->
        value_w_bit |> BitVec.zero_extend 32
        |> Value.entype (if sign then Type.int32 else Type.uint32)
    | 64 ->
        value_w_bit |> Value.entype (if sign then Type.int64 else Type.uint64)
    | _ -> failwith "not implemented"

  let to_int32 value = value |> to_intx 32

  let to_int64 value = value |> to_intx 64

  let to_uint32 value = value |> to_intx ~sign:false 32

  let to_uint64 value = value |> to_intx ~sign:false 64

  let to_tagged_signed value = value |> to_int32 |> Int32.to_tagged_signed

  let rem lval rval =
    let q = trunc (div lval rval) in
    let r_f64 = sub lval (mul q rval) in
    let is_inf_or_ninf num = Bool.ors [ is_inf num; is_ninf num ] in
    let is_zero_or_minus_zero num =
      Bool.ors [ is_zero num; is_minus_zero num ]
    in
    Bool.ite
      (* n = nan \/ d = nan -> nan *)
      (Bool.ors [ is_nan lval; is_nan rval ])
      nan
      (* n = inf \/ n = -inf -> nan *)
      (Bool.ite (is_inf_or_ninf lval) nan
         (Bool.ite
            (* d = inf \/ d = -inf -> n *)
            (is_inf_or_ninf rval)
            lval
            (Bool.ite
               (* d = zero \/ d = -zero -> nan *)
               (is_zero_or_minus_zero rval)
               nan
               (Bool.ite
                  (* n = zero \/ n = -zero -> n *)
                  (is_zero_or_minus_zero lval)
                  lval
                  (Bool.ite
                     (* r = 0 \/ n < -0 -> -0 else, r *)
                     (Bool.ands [ is_zero r_f64; lt lval minus_zero ])
                     minus_zero r_f64)))))

  let modulo = rem

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
        (evaluated |> from_value |> Model.eval model |> Real.to_decimal_string)
end
