open Z3utils
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
    (number |> Value.Int32.to_float64)
    (Bool.ite
       (number |> Value.has_type Type.uint32)
       (number |> Value.Uint32.to_float64)
       (Bool.ite
          (number |> Value.has_type Type.float64)
          number
          (Bool.ite
             (number |> Value.has_type Type.tagged_signed)
             (number |> Value.TaggedSigned.to_float64)
             (heap_number |> HeapNumber.to_float64))))

let to_uint32 mem number =
  let number_f64 = HeapNumber.load number mem |> HeapNumber.to_float64 in
  (* https://tc39.es/ecma262/#sec-touint32 *)
  Bool.ite
    (number |> Value.has_type Type.int32)
    (number |> Value.Int32.to_uint32)
    (Bool.ite
       (number |> Value.has_type Type.tagged_signed)
       (number |> Value.TaggedSigned.to_uint32)
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

let is_nan mem number =
  let n_f64 = number |> to_float64 mem in
  n_f64 |> Float64.is_nan

(* comparison *)
let eq lnum rnum mem =
  let lnum_f64 = lnum |> to_float64 mem in
  let rnum_f64 = rnum |> to_float64 mem in
  (* https://tc39.es/ecma262/#sec-numeric-types-number-equal *)
  Bool.ite
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
             Bool.tr Bool.fl)))

(* unary arith *)
let unary_minus mem number =
  Bool.ite (* https://tc39.es/ecma262/#sec-numeric-types-number-unaryMinus *)
    (number |> is_nan mem)
    Float64.nan
    (number |> to_float64 mem |> Float64.neg)

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

let imul lnum rnum mem =
  (* https://tc39.es/ecma262/#sec-math.imul *)
  Value.Uint32.mul (lnum |> to_uint32 mem) (rnum |> to_uint32 mem)
  |> Value.Uint32.to_int32

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

let subtract lnum rnum mem =
  (* https://tc39.es/ecma262/#sec-numeric-types-number-subtract *)
  add lnum (rnum |> unary_minus mem) mem

(* bitwise *)
let unsigned_right_shift x y mem =
  (* https://tc39.es/ecma262/#sec-numeric-types-number-unsignedRightShift *)
  let lnum = x |> to_uint32 mem in
  let rnum = y |> to_uint32 mem in
  let shift_count =
    Value.Uint32.modulo rnum (32 |> Value.from_int |> Value.cast Type.uint32)
  in
  Value.Uint32.lshr lnum shift_count

(* methods *)
let ceil mem number =
  let number_f64 = number |> to_float64 mem in
  (* https://tc39.es/ecma262/#sec-math.ceil *)
  Bool.ite
    (* [number] is integer -> [number] *)
    (Bool.ors
       [
         number_f64 |> Float64.is_integer;
         number_f64 |> Float64.is_nan;
         number_f64 |> Float64.is_zero;
         number_f64 |> Float64.is_minus_zero;
         number_f64 |> Float64.is_inf;
         number_f64 |> Float64.is_ninf;
       ])
    number
    (* -1 < [number] < -0 -> -0 *)
    (Bool.ite
       (Bool.ands
          [
            Float64.lt number_f64 Float64.minus_zero;
            Float64.gt number_f64 (Float64.from_float (Float.from_float (-1.0)));
          ])
       Float64.minus_zero
       (* else round([number],up) *)
       (Float64.round_up number_f64))
