open Z3utils
open ValueOperator
module HeapNumber = Objects.HeapNumber

(* Number ::= TaggedSigned | HeapNumber | Int32 | Uint32 | Float64 *)
let is_number value mem =
  Bool.ite
    (value |> Value.has_type Type.int32)
    Bool.tr
    (Bool.ite
       (value |> Value.has_type Type.uint32)
       Bool.tr
       (Bool.ite
          (value |> Value.has_type Type.float64)
          Bool.tr
          (Bool.ite
             (value |> Value.has_type Type.tagged_signed)
             Bool.tr
             (Bool.ite
                (Bool.ands
                   [
                     value |> Value.has_type Type.tagged_pointer;
                     value |> Objects.is_heap_number mem;
                   ])
                Bool.tr Bool.fl))))

let are_numbers values mem =
  Bool.ands (values |> List.rev_map (fun value -> is_number value mem))

let to_float64 mem number =
  let heap_number = HeapNumber.load number mem in
  Bool.ite
    (number |> Value.has_type Type.int32)
    (number |> Int32.to_float64)
    (Bool.ite
       (number |> Value.has_type Type.uint32)
       (number |> Uint32.to_float64)
       (Bool.ite
          (number |> Value.has_type Type.float64)
          number
          (Bool.ite
             (number |> Value.has_type Type.tagged_signed)
             (number |> TaggedSigned.to_float64)
             (heap_number |> HeapNumber.to_float64))))

let to_boolean mem number =
  let number_f64 = number |> to_float64 mem in
  (* https://tc39.es/ecma262/#sec-toboolean *)
  Bool.ite
    (Bool.ors
       [
         number_f64 |> Float64.is_nan;
         number_f64 |> Float64.is_zero;
         number_f64 |> Float64.is_minus_zero;
       ])
    Value.fl Value.tr

let to_uint32 mem number =
  let number_f64 = number |> to_float64 mem in
  (* https://tc39.es/ecma262/#sec-touint32 *)
  Bool.ite
    (number |> Value.has_type Type.int32)
    (number |> Int32.to_int Type.uint32 32)
    (Bool.ite
       (number |> Value.has_type Type.tagged_signed)
       (number |> TaggedSigned.to_uint32)
       (Bool.ite
          (number |> Value.has_type Type.uint32)
          number
          (number_f64 |> Float64.to_uint32)))

(* type check *)
let is_integer mem number =
  let heap_number = HeapNumber.load number mem in
  Bool.ite
    (Bool.ors
       [
         number |> Value.has_type Type.int32;
         number |> Value.has_type Type.uint32;
         number |> Value.has_type Type.tagged_signed;
       ])
    Bool.tr
    (Bool.ite
       (number |> Value.has_type Type.float64)
       (number |> Float64.is_integer)
       (heap_number |> HeapNumber.is_integer))

let is_minus_zero mem number =
  let n_f64 = number |> to_float64 mem in
  n_f64 |> Float64.is_minus_zero

let is_nan mem number =
  let n_f64 = number |> to_float64 mem in
  n_f64 |> Float64.is_nan

(* comparison *)
let equal lnum rnum mem =
  let lnum_f64 = lnum |> to_float64 mem in
  let rnum_f64 = rnum |> to_float64 mem in
  (* https://tc39.es/ecma262/#sec-numeric-types-number-equal *)
  Bool.ite
    (Bool.ite
       (* lnum = nan \/ rnum = nan -> false *)
       (Bool.ors [ Float64.is_nan lnum_f64; Float64.is_nan rnum_f64 ])
       Bool.fl
       (* lnum = rnum -> true *)
       (Bool.ite
          (Float64.eq lnum_f64 rnum_f64)
          Bool.tr
          (Bool.ite
             (* lnum = -0 /\ rnum = 0 -> true *)
             (Bool.ands
                [ Float64.is_minus_zero lnum_f64; Float64.is_zero rnum_f64 ])
             Bool.tr
             (* lnum = 0 /\ rnum = -0 -> true *)
             (Bool.ite
                (Bool.ands
                   [ Float64.is_minus_zero rnum_f64; Float64.is_zero lnum ])
                Bool.tr Bool.fl))))
    Value.tr Value.fl

let less_than lnum rnum mem =
  (* https://tc39.es/ecma262/#sec-numeric-types-number-lessThan *)
  let lnum_f64 = lnum |> to_float64 mem in
  let rnum_f64 = rnum |> to_float64 mem in
  Bool.ite
    (Bool.ors [ lnum_f64 |> Float64.is_nan; rnum_f64 |> Float64.is_nan ])
    Value.undefined
    (Bool.ite (Float64.lt lnum_f64 rnum_f64) Value.tr Value.fl)

let same_value lnum rnum mem =
  (* https://tc39.es/ecma262/#sec-numeric-types-number-sameValue *)
  let lnum_f64 = lnum |> to_float64 mem in
  let rnum_f64 = rnum |> to_float64 mem in
  Bool.ite
    (Bool.ite
       (Bool.ors [ lnum_f64 |> Float64.is_nan; rnum_f64 |> Float64.is_nan ])
       Bool.tr
       (Bool.ite
          (Bool.ands
             [ lnum_f64 |> Float64.is_zero; rnum_f64 |> Float64.is_minus_zero ])
          Bool.fl
          (Bool.ite
             (Bool.ands
                [
                  rnum_f64 |> Float64.is_zero; lnum_f64 |> Float64.is_minus_zero;
                ])
             Bool.fl
             (Float64.eq lnum_f64 rnum_f64))))
    Value.tr Value.fl

(* unary arith *)
let abs mem number =
  (* https://tc39.es/ecma262/#sec-math.abs *)
  let num_f64 = number |> to_float64 mem in
  (* nan -> nan *)
  Bool.ite (Float64.is_nan num_f64) Float64.nan
    (* -0 -> 0 *)
    (Bool.ite
       (Float64.is_minus_zero num_f64)
       Float64.zero
       (* ninf -> inf *)
       (Bool.ite
          (num_f64 |> Float64.is_ninf)
          Float64.inf
          (* n < 0 -> -n *)
          (Bool.ite (Float64.is_negative num_f64) (Float64.neg num_f64) num_f64)))

let unary_minus mem number =
  let num_f64 = number |> to_float64 mem in
  (* https://tc39.es/ecma262/#sec-numeric-types-number-unaryMinus *)
  Bool.ite (num_f64 |> Float64.is_nan) Float64.nan (num_f64 |> Float64.neg)

(* binary arith *)
let add lnum rnum mem =
  (* https://tc39.es/ecma262/#sec-numeric-types-number-add *)
  let lnum_f64 = lnum |> to_float64 mem in
  let rnum_f64 = rnum |> to_float64 mem in
  (* if lnum or rnum is nan, return nan *)
  Bool.ite
    (Bool.ors [ Float64.is_nan lnum_f64; Float64.is_nan rnum_f64 ])
    Float64.nan
    (* inf+ninf = nan *)
    (Bool.ite
       (Bool.ands [ Float64.is_inf lnum_f64; Float64.is_ninf rnum_f64 ])
       Float64.nan
       (* ninf+inf = nan *)
       (Bool.ite
          (Bool.ands [ Float64.is_ninf lnum_f64; Float64.is_inf rnum_f64 ])
          Float64.nan
          (* lnum is inf or -inf, return lnum*)
          (Bool.ite
             (Bool.ors [ Float64.is_inf lnum_f64; Float64.is_ninf lnum_f64 ])
             lnum_f64
             (* rnum is inf or -inf, return rnum*)
             (Bool.ite
                (Bool.ors [ Float64.is_inf rnum_f64; Float64.is_ninf rnum_f64 ])
                rnum_f64
                (* -0 + -0 = -0 *)
                (Bool.ite
                   (Bool.ands
                      [
                        Float64.is_minus_zero lnum_f64;
                        Float64.is_minus_zero rnum_f64;
                      ])
                   Float64.minus_zero
                   (* else, n+n *)
                   (Float64.add lnum_f64 rnum_f64))))))

let subtract lnum rnum mem =
  (* https://tc39.es/ecma262/#sec-numeric-types-number-subtract *)
  add lnum (rnum |> unary_minus mem) mem

let divide lnum rnum mem =
  (* https://tc39.es/ecma262/#sec-numeric-types-number-divide *)
  let lnum_f64 = lnum |> to_float64 mem in
  let rnum_f64 = rnum |> to_float64 mem in
  (* if lnum or rnum is nan, return nan *)
  Bool.ite
    (Bool.ors [ Float64.is_nan lnum_f64; Float64.is_nan rnum_f64 ])
    Float64.nan
    (Bool.ite
       (* inf / inf, inf / ninf, ninf / inf, ninf / ninf = nan *)
       (Bool.ors [ Float64.is_inf lnum_f64; Float64.is_ninf lnum_f64 ])
       (Bool.ite
          (Bool.ors [ Float64.is_inf rnum_f64; Float64.is_ninf rnum_f64 ])
          Float64.nan
          (Bool.ite
             (Bool.ors
                [ Float64.is_zero rnum_f64; Float64.is_positive rnum_f64 ])
             lnum_f64 (Float64.neg lnum_f64)))
       (Bool.ite (Float64.is_inf rnum_f64)
          (Bool.ite
             (Bool.ors
                [ Float64.is_zero lnum_f64; Float64.is_positive lnum_f64 ])
             Float64.zero Float64.minus_zero)
          (Bool.ite (Float64.is_ninf rnum_f64)
             (Bool.ite
                (Bool.ors
                   [ Float64.is_zero lnum_f64; Float64.is_positive lnum_f64 ])
                Float64.minus_zero Float64.zero)
             (Bool.ite
                (Bool.ors
                   [ Float64.is_zero lnum_f64; Float64.is_minus_zero lnum_f64 ])
                (Bool.ite
                   (Bool.ors
                      [
                        Float64.is_zero rnum_f64; Float64.is_minus_zero rnum_f64;
                      ])
                   Float64.nan
                   (Bool.ite
                      (Float64.is_positive rnum_f64)
                      lnum_f64 (Float64.neg lnum_f64)))
                (Bool.ite (Float64.is_zero rnum_f64)
                   (Bool.ite
                      (Float64.is_positive lnum_f64)
                      Float64.inf Float64.ninf)
                   (Bool.ite
                      (Float64.is_minus_zero rnum_f64)
                      (Bool.ite
                         (Float64.is_positive lnum_f64)
                         Float64.ninf Float64.inf)
                      (Float64.div lnum_f64 rnum_f64)))))))

let multiply lnum rnum mem =
  (* https://tc39.es/ecma262/#sec-numeric-types-number-multiply *)
  let lnum_f64 = lnum |> to_float64 mem in
  let rnum_f64 = rnum |> to_float64 mem in

  let if_l_is_inf_or_ninf l r =
    Bool.ite
      (Bool.ors [ Float64.is_zero r; Float64.is_minus_zero r ])
      Float64.nan
      (Bool.ite (Float64.is_positive r) l (l |> Float64.neg))
  in

  let if_minus_zero n =
    Bool.ite
      (Bool.ors [ Float64.is_minus_zero n; Float64.is_negative n ])
      Float64.zero Float64.minus_zero
  in

  Bool.ite
    (* if lnum or rnum is nan, return nan *)
    (Bool.ors [ Float64.is_nan lnum_f64; Float64.is_nan rnum_f64 ])
    Float64.nan
    (* if lnum is inf or -inf *)
    (Bool.ite
       (Bool.ors [ Float64.is_inf lnum_f64; Float64.is_ninf lnum_f64 ])
       (if_l_is_inf_or_ninf lnum_f64 rnum_f64)
       (* if rnum is inf or -inf *)
       (Bool.ite
          (Bool.ors [ Float64.is_inf rnum_f64; Float64.is_ninf rnum_f64 ])
          (if_l_is_inf_or_ninf rnum_f64 lnum_f64)
          (* if lnum is -0 *)
          (Bool.ite
             (Float64.is_minus_zero lnum_f64)
             (if_minus_zero rnum_f64)
             (* if rnum is -0 *)
             (Bool.ite
                (Float64.is_minus_zero rnum_f64)
                (if_minus_zero lnum_f64)
                (* else, return lnum * rnum *)
                (Float64.mul lnum_f64 rnum_f64)))))

let imul lnum rnum mem =
  (* https://tc39.es/ecma262/#sec-math.imul *)
  Uint32.mul (lnum |> to_uint32 mem) (rnum |> to_uint32 mem)
  |> Uint32.to_int Type.int32 32

let remainder n d mem =
  (* https://tc39.es/ecma262/#sec-numeric-types-number-remainder *)
  let n_f64 = n |> to_float64 mem in
  let d_f64 = d |> to_float64 mem in
  let r_f64 =
    let q_f64 = Float64.div n_f64 d_f64 in
    Float64.sub n_f64 (Float64.mul d_f64 (q_f64 |> Float64.trunc))
  in

  let is_inf_or_ninf num =
    Bool.ors [ Float64.is_inf num; Float64.is_ninf num ]
  in
  let is_zero_or_minus_zero num =
    Bool.ors [ Float64.is_zero num; Float64.is_minus_zero num ]
  in
  Bool.ite
    (* n = nan \/ d = nan -> nan *)
    (Bool.ors [ Float64.is_nan n_f64; Float64.is_nan d_f64 ])
    Float64.nan
    (* n = inf \/ n = -inf -> nan *)
    (Bool.ite (is_inf_or_ninf n_f64) Float64.nan
       (Bool.ite
          (* d = inf \/ d = -inf -> n *)
          (is_inf_or_ninf d_f64)
          n_f64
          (Bool.ite
             (* d = zero \/ d = -zero -> nan *)
             (is_zero_or_minus_zero d_f64)
             Float64.nan
             (Bool.ite
                (* n = zero \/ n = -zero -> n *)
                (is_zero_or_minus_zero n_f64)
                n_f64
                (Bool.ite
                   (* r = 0 \/ n < -0 -> -0 else, r *)
                   (Bool.ands
                      [
                        Float64.is_zero r_f64;
                        Float64.lt n_f64 Float64.minus_zero;
                      ])
                   Float64.minus_zero r_f64)))))

(* bitwise *)
let bitwise op x y mem =
  (* https://tc39.es/ecma262/#sec-numberbitwiseop *)
  let lnum = x |> to_float64 mem |> Float64.to_int32 in
  let rnum = y |> to_float64 mem |> Float64.to_int32 in
  match op with
  | "&" -> Word32.and_ lnum rnum
  | "|" -> Word32.or_ lnum rnum
  | "^" -> Word32.xor lnum rnum
  | _ -> failwith "unreachable"

let unsigned_right_shift x y mem =
  (* https://tc39.es/ecma262/#sec-numeric-types-number-unsignedRightShift *)
  let lnum = x |> to_uint32 mem in
  let rnum = y |> to_uint32 mem in
  let shift_count =
    Uint32.modulo rnum (32 |> Value.from_int |> Value.cast Type.uint32)
  in
  Uint32.lshr lnum shift_count

(* methods *)
let max lnum rnum mem =
  (* https://tc39.es/ecma262/#sec-math.max *)
  let lnum_f64 = lnum |> to_float64 mem in
  let rnum_f64 = rnum |> to_float64 mem in
  Bool.ite
    (* nan, nan -> nan *)
    (Bool.ors [ lnum_f64 |> Float64.is_nan; rnum_f64 |> Float64.is_nan ])
    Float64.nan
    (Bool.ite
       (* -0, 0 -> 0 *)
       (Bool.ands
          [ lnum_f64 |> Float64.is_minus_zero; rnum_f64 |> Float64.is_zero ])
       Float64.zero
       (Bool.ite
          (* 0, -0 -> 0 *)
          (Bool.ands
             [ lnum_f64 |> Float64.is_zero; rnum_f64 |> Float64.is_minus_zero ])
          Float64.zero
          (* n1, n2 -> n1 > n2 ? n1 : n2 *)
          (Bool.ite (Float64.gt lnum_f64 rnum_f64) lnum_f64 rnum_f64)))

let min lnum rnum mem =
  (* https://tc39.es/ecma262/#sec-math.min *)
  let lnum_f64 = lnum |> to_float64 mem in
  let rnum_f64 = rnum |> to_float64 mem in
  Bool.ite
    (* nan, nan -> nan *)
    (Bool.ors [ lnum_f64 |> Float64.is_nan; rnum_f64 |> Float64.is_nan ])
    Float64.nan
    (Bool.ite
       (* -0, 0 -> -0 *)
       (Bool.ands
          [ lnum_f64 |> Float64.is_minus_zero; rnum_f64 |> Float64.is_zero ])
       Float64.minus_zero
       (Bool.ite
          (* 0, -0 -> -0 *)
          (Bool.ands
             [ lnum_f64 |> Float64.is_zero; rnum_f64 |> Float64.is_minus_zero ])
          Float64.minus_zero
          (* n1, n2 -> n1 < n2 ? n1 : n2 *)
          (Bool.ite (Float64.lt lnum_f64 rnum_f64) lnum_f64 rnum_f64)))

let sign mem number =
  let n_f64 = number |> to_float64 mem in
  (* https://tc39.es/ecma262/#sec-math.sign *)
  Bool.ite
    (* [number] is nan, zero or minus_zero -> [number] *)
    (Bool.ors
       [
         n_f64 |> Float64.is_nan;
         n_f64 |> Float64.is_zero;
         n_f64 |> Float64.is_minus_zero;
       ])
    n_f64
    (Bool.ite
       (* [number] < -0 -> -1 else 1 *)
       (Float64.lt n_f64 Float64.minus_zero)
       (Float64.neg Float64.one) Float64.one)

let ceil mem number =
  let number_f64 = number |> to_float64 mem in
  (* https://tc39.es/ecma262/#sec-math.ceil *)
  Bool.ite
    (* integer, nan, zero, minus zero, inf, ninf -> [number] *)
    (Bool.ors
       [
         number_f64 |> Float64.is_integer;
         number_f64 |> Float64.is_nan;
         number_f64 |> Float64.is_zero;
         number_f64 |> Float64.is_minus_zero;
         number_f64 |> Float64.is_inf;
         number_f64 |> Float64.is_ninf;
       ])
    number_f64
    (* -1 < [number] < -0 -> -0 *)
    (Bool.ite
       (Bool.ands
          [
            Float64.lt number_f64 Float64.minus_zero;
            Float64.gt number_f64 (Float64.from_numeral (-1.0));
          ])
       Float64.minus_zero
       (* else round to positive inf *)
       (Float64.ceil number_f64))

let floor mem number =
  let number_f64 = number |> to_float64 mem in
  (* https://tc39.es/ecma262/#sec-math.floor *)
  Bool.ite
    (* integer, nan, zero, minus zero, inf, ninf -> [number] *)
    (Bool.ors
       [
         number_f64 |> Float64.is_integer;
         number_f64 |> Float64.is_nan;
         number_f64 |> Float64.is_zero;
         number_f64 |> Float64.is_minus_zero;
         number_f64 |> Float64.is_inf;
         number_f64 |> Float64.is_ninf;
       ])
    number_f64
    (* 0 < [number] < 1 -> 0 *)
    (Bool.ite
       (Bool.ands
          [
            Float64.gt number_f64 Float64.zero;
            Float64.lt number_f64 (Float64.from_numeral 1.0);
          ])
       Float64.zero
       (* else round to negative inf *)
       (Float64.floor number_f64))

let round mem number =
  (* https://tc39.es/ecma262/#sec-math.round *)
  let n_f64 = number |> to_float64 mem in
  Bool.ite
    (* nan, inf, ninf, integer -> [number]  *)
    (Bool.ors
       [
         n_f64 |> Float64.is_nan;
         n_f64 |> Float64.is_inf;
         n_f64 |> Float64.is_ninf;
         n_f64 |> Float64.is_integer;
       ])
    n_f64
    (Bool.ite
       (* 0 < [number] < 0.5 -> 0 *)
       (Bool.ands
          [
            Float64.lt n_f64 (0.5 |> Float64.from_numeral);
            Float64.gt n_f64 Float64.zero;
          ])
       Float64.zero
       (Bool.ite
          (* -0.5 <= [number] < -0 -> -0 *)
          (Bool.ands
             [
               Float64.lt n_f64 Float64.minus_zero;
               Float64.ge n_f64 (Float64.from_numeral (-0.5));
             ])
          Float64.minus_zero
          (Bool.ite
             (* tie -> [number] + 0.5 ; half up *)
             (Float64.mul n_f64 (Float64.from_numeral 2.0) |> Float64.is_integer)
             (Float64.add n_f64 (Float64.from_numeral 0.5))
             (* else round to nearest *)
             (n_f64 |> Float64.round_nearest_to_even))))

let trunc num mem =
  (* https://tc39.es/ecma262/#sec-math.trunc *)
  let num_f64 = num |> to_float64 mem in
  Bool.ite
    (Bool.ors
       [
         num_f64 |> Float64.is_nan;
         num_f64 |> Float64.is_zero;
         num_f64 |> Float64.is_minus_zero;
         num_f64 |> Float64.is_inf;
         num_f64 |> Float64.is_ninf;
       ])
    num_f64
    (Bool.ite
       (Bool.ands
          [
            Float64.lt num_f64 (1.0 |> Float64.from_numeral);
            Float64.gt num_f64 Float64.zero;
          ])
       Float64.zero
       (Bool.ite
          (Bool.ands
             [
               Float64.gt num_f64 (-1.0 |> Float64.from_numeral);
               Float64.lt num_f64 Float64.minus_zero;
             ])
          Float64.minus_zero (num_f64 |> Float64.trunc)))

let sin mem number =
  let n_f64 = number |> to_float64 mem in
  n_f64 |> Float64.sin

let expm1 mem number =
  let n_f64 = number |> to_float64 mem in
  n_f64 |> Float64.expm1
