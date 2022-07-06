open Z3utils

let to_float value = value |> Value.data_of |> Z3utils.Float.from_ieee_bv

let from_float t = t |> Z3utils.Float.to_ieee_bv |> Value.entype Type.float64

let to_int64 value =
  value |> to_float
  |> Z3utils.Float.to_sbv Z3utils.Float.rne_mode
  |> Value.entype Type.int64

let to_int32 value =
  value |> to_float
  |> Z3utils.Float.to_sbv ~len:32 Z3utils.Float.rne_mode
  |> BitVec.sign_extend 32 |> Value.entype Type.int32

let to_tagged_signed value = value |> to_int32 |> Value.Int32.to_tagged_signed

let to_string model value =
  let v_str = value |> to_float |> Model.eval model |> Real.to_decimal_string in
  Format.sprintf "Float64(%s)" v_str

let is_minus_zero value = Float.is_minus_zero (value |> to_float)

let is_positive value =
  BitVec.eqi (BitVec.extract 63 63 (value |> Value.data_of)) 0

let is_negative value =
  BitVec.eqi (BitVec.extract 63 63 (value |> Value.data_of)) 0

let nan = Float.nan () |> from_float

let ninf = Float.ninf () |> from_float

let inf = Float.inf () |> from_float

let zero = Float.from_float 0.0 |> from_float

let one = Float.from_float 1.0 |> from_float

let minus_zero = Float.minus_zero () |> from_float

let eq lval rval =
  let lf = lval |> to_float in
  let rf = rval |> to_float in
  Z3utils.Float.eq lf rf

let add lval rval =
  let lf = lval |> to_float in
  let rf = rval |> to_float in
  Z3utils.Float.add lf rf |> from_float

let sub lval rval =
  let lf = lval |> to_float in
  let rf = rval |> to_float in
  Z3utils.Float.sub lf rf |> from_float

let mul lval rval =
  let lf = lval |> to_float in
  let rf = rval |> to_float in
  Z3utils.Float.mul lf rf |> from_float

let lt lval rval =
  let lf = lval |> to_float in
  let rf = rval |> to_float in
  Z3utils.Float.lt lf rf

let le lval rval =
  let lf = lval |> to_float in
  let rf = rval |> to_float in
  Z3utils.Float.le lf rf

let gt lval rval =
  let lf = lval |> to_float in
  let rf = rval |> to_float in
  Z3utils.Float.gt lf rf

let ge lval rval =
  let lf = lval |> to_float in
  let rf = rval |> to_float in
  Z3utils.Float.ge lf rf

let neg value =
  let f = value |> to_float in
  Z3utils.Float.neg f |> from_float

let round value = Z3utils.Float.round Z3utils.Float.rne_mode (value |> to_float)

let is_integer value = eq value (value |> round |> from_float)

let safe_integer_max = Float.safe_integer_max () |> from_float

let safe_integer_min = Float.safe_integer_min () |> from_float

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
