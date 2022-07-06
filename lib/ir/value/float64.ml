open Z3utils

(* conversion *)
let from_float f = f |> Z3utils.Float.to_ieee_bv |> Value.entype Type.float64

let to_float value = value |> Value.data_of |> Z3utils.Float.from_ieee_bv

let to_intx width value =
  let value_int =
    let f = value |> to_float in
    let i_mod_2_32 =
      Bool.ite (Float.is_negative f)
        (Integer.mod_
           (f |> Float.abs |> Float.floor |> Float.neg |> Float.to_real
          |> Real.to_integer)
           (Integer.from_int (Utils.pow 2 32)))
        (Integer.mod_
           (f |> Float.abs |> Float.floor |> Float.to_real |> Real.to_integer)
           (Integer.from_int (Utils.pow 2 32)))
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
         (Integer.ge i_mod_2_32 (Integer.from_int (Utils.pow 2 31)))
         (Integer.sub i_mod_2_32 (Integer.from_int (Utils.pow 2 32)))
         i_mod_2_32)
  in
  match width with
  | 32 ->
      value_int |> Integer.to_bv ~len:32 |> BitVec.zero_extend 32
      |> Value.entype Type.int32
  | 64 -> value_int |> Integer.to_bv ~len:64 |> Value.entype Type.int64
  | _ -> failwith "not implemented"

let to_int32 value = value |> to_intx 32

let to_int64 value = value |> to_intx 64

let to_tagged_signed value = value |> to_int32 |> Value.Int32.to_tagged_signed

(* pp *)
let to_string model value =
  let v_str = value |> to_float |> Model.eval model |> Real.to_decimal_string in
  Format.sprintf "Float64(%s)" v_str

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
  Z3utils.Float.add lf rf |> from_float

let floor value = Float.floor (value |> to_float) |> from_float

let mul lval rval =
  let lf = lval |> to_float in
  let rf = rval |> to_float in
  Z3utils.Float.mul lf rf |> from_float

let neg value =
  let f = value |> to_float in
  Z3utils.Float.neg f |> from_float

let round value = Float.round Float.rne_mode (value |> to_float)

let sub lval rval =
  let lf = lval |> to_float in
  let rf = rval |> to_float in
  Z3utils.Float.sub lf rf |> from_float

(* comparison *)
let eq lval rval =
  let lf = lval |> to_float in
  let rf = rval |> to_float in
  Z3utils.Float.eq lf rf

let le lval rval =
  let lf = lval |> to_float in
  let rf = rval |> to_float in
  Z3utils.Float.le lf rf

let lt lval rval =
  let lf = lval |> to_float in
  let rf = rval |> to_float in
  Z3utils.Float.lt lf rf

let ge lval rval =
  let lf = lval |> to_float in
  let rf = rval |> to_float in
  Z3utils.Float.ge lf rf

let gt lval rval =
  let lf = lval |> to_float in
  let rf = rval |> to_float in
  Z3utils.Float.gt lf rf

(* methods *)

let is_integer value = eq value (value |> round |> from_float)

let is_minus_zero value = Float.is_minus_zero (value |> to_float)

let is_negative value =
  BitVec.eqi (BitVec.extract 63 63 (value |> Value.data_of)) 0

let is_positive value =
  BitVec.eqi (BitVec.extract 63 63 (value |> Value.data_of)) 0

let is_safe_integer value =
  Z3utils.Bool.ands
    [ is_integer value; ge value safe_integer_min; le value safe_integer_max ]

let can_be_smi value =
  Z3utils.Bool.ands
    [
      value |> is_integer;
      Z3utils.Bool.not (value |> is_minus_zero);
      value |> to_int32 |> Value.Int32.is_in_smi_range;
    ]
