open Z3utils
module HeapNumber = Objects.HeapNumber
module Repr = MachineType.Repr

let has_type_all ty values =
  Bool.ands (List.map (fun v -> Value.has_type ty v) values)

(* simplified: numeric *)
let number_abs vid nptr next_bid mem =
  let value = Value.init vid in
  let deopt_cond =
    Bool.not
      (Bool.ands
         [
           nptr |> Value.has_type Type.tagged_pointer;
           Objects.is_heap_number nptr !mem;
         ])
  in
  (* https://tc39.es/ecma262/#sec-math.abs *)
  let abs =
    let n = HeapNumber.load nptr !mem in
    (* nan -> nan *)
    Bool.ite (HeapNumber.is_nan n) Float64.nan
      (* -0 -> 0 *)
      (Bool.ite
         (HeapNumber.is_minus_zero n)
         Float64.zero
         (* ninf -> inf *)
         (Bool.ite (HeapNumber.is_ninf n) Float64.inf
            (* n < 0 -> -n *)
            (Bool.ite (HeapNumber.is_negative n)
               (Float64.neg (n.value |> Value.entype Type.float64))
               (n.value |> Value.entype Type.float64))))
    |> HeapNumber.from_float64 next_bid (Bool.not deopt_cond) mem
  in
  let assertion = Value.eq value abs in
  (value, Control.empty, assertion, Bool.fl, deopt_cond)

let number_add vid lval rval next_bid mem =
  let value = Value.init vid in
  let deopt_cond =
    Bool.not
      (Bool.ands
         [
           lval |> Value.has_type Type.tagged_pointer;
           rval |> Value.has_type Type.tagged_pointer;
           Objects.is_heap_number lval !mem;
           Objects.is_heap_number rval !mem;
         ])
  in
  (* https://tc39.es/ecma262/#sec-numeric-types-number-add *)
  let add =
    let lnum = HeapNumber.load lval !mem in
    let rnum = HeapNumber.load rval !mem in
    (* if lnum or rnum is nan, return nan *)
    Bool.ite
      (Bool.ors [ HeapNumber.is_nan lnum; HeapNumber.is_nan rnum ])
      Float64.nan
      (* inf+ninf = nan *)
      (Bool.ite
         (Bool.ands [ HeapNumber.is_inf lnum; HeapNumber.is_ninf rnum ])
         Float64.nan
         (* ninf+inf = nan *)
         (Bool.ite
            (Bool.ands [ HeapNumber.is_ninf lnum; HeapNumber.is_inf rnum ])
            Float64.nan
            (* lnum is inf or -inf, return lnum*)
            (Bool.ite
               (Bool.ors [ HeapNumber.is_inf lnum; HeapNumber.is_ninf lnum ])
               (lnum.value |> Value.entype Type.float64)
               (* rnum is inf or -inf, return rnum*)
               (Bool.ite
                  (Bool.ors [ HeapNumber.is_inf rnum; HeapNumber.is_ninf rnum ])
                  (rnum.value |> Value.entype Type.float64)
                  (* -0 + -0 = -0 *)
                  (Bool.ite
                     (Bool.ands
                        [
                          HeapNumber.is_minus_zero lnum;
                          HeapNumber.is_minus_zero rnum;
                        ])
                     Float64.minus_zero
                     (* else, n+n *)
                     (Float64.add lnum.value rnum.value))))))
    |> HeapNumber.from_float64 next_bid (Bool.not deopt_cond) mem
  in

  let assertion = Value.eq value add in
  (value, Control.empty, assertion, Bool.fl, deopt_cond)

let number_expm1 vid nptr next_bid mem =
  let value = Value.init vid in
  let deopt_cond =
    Bool.not
      (Bool.ands
         [
           nptr |> Value.has_type Type.tagged_pointer;
           Objects.is_heap_number nptr !mem;
         ])
  in
  (* https://tc39.es/ecma262/#sec-math.expm1 *)
  let expm1 =
    let num = HeapNumber.load nptr !mem in
    let bv_sort = BV.mk_sort ctx 64 in
    let expm_decl =
      Z3.FuncDecl.mk_func_decl_s ctx "unknown_number_expm1" [ bv_sort ] bv_sort
    in
    (* if num is NaN or 0 or -0 or inf, return num*)
    Bool.ite
      (Bool.ors
         [
           HeapNumber.is_nan num;
           HeapNumber.is_zero num;
           HeapNumber.is_minus_zero num;
           HeapNumber.is_inf num;
         ])
      (num |> HeapNumber.to_float64)
      (* if num is -inf, return -1 *)
      (Bool.ite (HeapNumber.is_ninf num)
         (Float.from_float (-1.0) |> Float64.from_float)
         (Z3.FuncDecl.apply expm_decl [ num.value ] |> Value.entype Type.float64))
    |> HeapNumber.from_float64 next_bid (Bool.not deopt_cond) mem
  in

  let assertion = Value.eq value expm1 in
  (value, Control.empty, assertion, Bool.fl, deopt_cond)

let number_max vid lval rval next_bid mem =
  let value = Value.init vid in
  let deopt_cond =
    Bool.not
      (Bool.ands
         [
           lval |> Value.has_type Type.tagged_pointer;
           rval |> Value.has_type Type.tagged_pointer;
           Objects.is_heap_number lval !mem;
           Objects.is_heap_number rval !mem;
         ])
  in
  (* https://tc39.es/ecma262/#sec-math.max *)
  let max =
    let lnum = HeapNumber.load lval !mem in
    let rnum = HeapNumber.load rval !mem in
    Bool.ite
      (* if lnum or rnum is nan, return nan *)
      (Bool.ors [ HeapNumber.is_nan lnum; HeapNumber.is_nan rnum ])
      Float64.nan
      (* if lnum is -0 and rnum is 0, return 0 *)
      (Bool.ite
         (Bool.ands [ HeapNumber.is_minus_zero lnum; HeapNumber.is_zero rnum ])
         Float64.zero
         (* if lnum is 0 and rnum is -0, return 0 *)
         (Bool.ite
            (Bool.ands
               [ HeapNumber.is_zero lnum; HeapNumber.is_minus_zero rnum ])
            Float64.zero
            (* if lnum < rnum, return rnum else return lnum *)
            (Bool.ite (HeapNumber.lt lnum rnum)
               (rnum |> HeapNumber.to_float64)
               (lnum |> HeapNumber.to_float64))))
    |> HeapNumber.from_float64 next_bid (Bool.not deopt_cond) mem
  in

  let assertion = Value.eq value max in
  (value, Control.empty, assertion, Bool.fl, deopt_cond)

let number_min vid lval rval next_bid mem =
  let value = Value.init vid in
  let deopt_cond =
    Bool.not
      (Bool.ands
         [
           lval |> Value.has_type Type.tagged_pointer;
           rval |> Value.has_type Type.tagged_pointer;
           Objects.is_heap_number lval !mem;
           Objects.is_heap_number rval !mem;
         ])
  in
  (* https://tc39.es/ecma262/#sec-math.min *)
  let min =
    let lnum = HeapNumber.load lval !mem in
    let rnum = HeapNumber.load rval !mem in
    Bool.ite
      (* if lnum or rnum is nan, return nan *)
      (Bool.ors [ HeapNumber.is_nan lnum; HeapNumber.is_nan rnum ])
      Float64.nan
      (* if lnum is -0 and rnum is 0, return -0 *)
      (Bool.ite
         (Bool.ands [ HeapNumber.is_minus_zero lnum; HeapNumber.is_zero rnum ])
         Float64.minus_zero
         (* if lnum is 0 and rnum is -0, return -0 *)
         (Bool.ite
            (Bool.ands
               [ HeapNumber.is_zero lnum; HeapNumber.is_minus_zero rnum ])
            Float64.minus_zero
            (* if lnum < rnum, return lnum else return rnum *)
            (Bool.ite (HeapNumber.lt lnum rnum)
               (lnum |> HeapNumber.to_float64)
               (rnum |> HeapNumber.to_float64))))
    |> HeapNumber.from_float64 next_bid (Bool.not deopt_cond) mem
  in

  let assertion = Value.eq value min in
  (value, Control.empty, assertion, Bool.fl, deopt_cond)

let number_multiply vid lval rval next_bid mem =
  let value = Value.init vid in
  let deopt_cond =
    Bool.not
      (Bool.ands
         [
           lval |> Value.has_type Type.tagged_pointer;
           rval |> Value.has_type Type.tagged_pointer;
           Objects.is_heap_number lval !mem;
           Objects.is_heap_number rval !mem;
         ])
  in
  (* https://tc39.es/ecma262/#sec-math.multiply *)
  let multiply =
    let lnum = HeapNumber.load lval !mem in
    let rnum = HeapNumber.load rval !mem in

    let if_l_is_inf_or_ninf l r =
      Bool.ite
        (Bool.ors [ HeapNumber.is_zero r; HeapNumber.is_minus_zero r ])
        Float64.nan
        (Bool.ite (HeapNumber.is_positive r)
           (l |> HeapNumber.to_float64)
           (l |> HeapNumber.to_float64 |> Float64.neg))
    in

    let if_minus_zero n =
      Bool.ite
        (Bool.ors [ HeapNumber.is_minus_zero n; HeapNumber.is_negative n ])
        Float64.zero Float64.minus_zero
    in

    Bool.ite
      (* if lnum or rnum is nan, return nan *)
      (Bool.ors [ HeapNumber.is_nan lnum; HeapNumber.is_nan rnum ])
      Float64.nan
      (* if lnum is inf or -inf *)
      (Bool.ite
         (Bool.ors [ HeapNumber.is_inf lnum; HeapNumber.is_ninf lnum ])
         (if_l_is_inf_or_ninf lnum rnum)
         (* if rnum is inf or -inf *)
         (Bool.ite
            (Bool.ors [ HeapNumber.is_inf rnum; HeapNumber.is_ninf rnum ])
            (if_l_is_inf_or_ninf rnum lnum)
            (* if lnum is -0 *)
            (Bool.ite
               (HeapNumber.is_minus_zero lnum)
               (if_minus_zero rnum)
               (* if rnum is -0 *)
               (Bool.ite
                  (HeapNumber.is_minus_zero rnum)
                  (if_minus_zero lnum)
                  (* else, return lnum * rnum *)
                  (Float64.mul
                     (lnum |> HeapNumber.to_float64)
                     (rnum |> HeapNumber.to_float64))))))
    |> HeapNumber.from_float64 next_bid (Bool.not deopt_cond) mem
  in

  let assertion = Value.eq value multiply in
  (value, Control.empty, assertion, Bool.fl, deopt_cond)

let speculative_number_add vid lval rval next_bid mem =
  (* [TODO] handle deoptimization *)
  number_add vid lval rval next_bid mem

let speculative_number_multiply vid lval rval next_bid mem =
  (* [TODO] handle deoptimization *)
  number_multiply vid lval rval next_bid mem

(* well-defined condition:
 * (IsTaggedSigned(lval) /\ IsTaggedSigned(rval))
 * \/ (IsTaggedPointer(lval) /\ IsTaggedPointer(rval)
 *    /\ PointsNumberObject(lval) /\ PointsNumberObject(rval)
 *    /\ IsAdditiveSafeInteger(lval) /\ IsAdditiveSafeInteger(rval))
 * assertion:
 *  value = ite well-defined (lval+rval) UB *)
let speculative_safe_integer_add vid lval rval next_bid mem =
  let value = Value.init vid in

  let deopt_cond =
    let is_safe_integer value =
      Bool.ors
        [
          value |> Value.has_type Type.tagged_signed;
          Bool.ands
            [
              value |> Value.has_type Type.tagged_pointer;
              Objects.is_heap_number value !mem;
              HeapNumber.is_safe_integer (HeapNumber.load value !mem);
            ];
        ]
    in
    Bool.not (Bool.ands [ is_safe_integer lval; is_safe_integer rval ])
  in

  let added_f64 =
    let value_to_float64 value =
      let number = HeapNumber.load value !mem in
      Bool.ite
        (value |> Value.has_type Type.tagged_signed)
        (Value.TaggedSigned.to_float64 value)
        (number.value |> Value.entype Type.float64)
    in
    let lf = lval |> value_to_float64 in
    let rf = rval |> value_to_float64 in
    Float64.add lf rf
  in

  let res =
    added_f64 |> HeapNumber.from_float64 next_bid (Bool.not deopt_cond) mem
  in

  let assertion = Value.eq value res in
  (value, Control.empty, assertion, Bool.fl, deopt_cond)

(* well-defined condition:
 * - IsTaggedPointer(lval) /\ IsTaggedPointer(rval)
 * - PointsNumberObject(lval) /\ PointsNumberObject(rval)
 * - IsSafeInteger(lval) /\ IsSafeInteger(rval)
 * - IsWellDefined(lval) /\ IsWellDefined(rval)
 * assertion:
 *  value = ite well-defined (lval-rval) UB *)
let speculative_safe_integer_subtract vid lval rval next_bid mem =
  let value = Value.init vid in

  let lnum = HeapNumber.load lval !mem in
  let rnum = HeapNumber.load rval !mem in

  let deopt_cond =
    Bool.not
      (Bool.ands
         [
           lval |> Value.has_type Type.tagged_pointer;
           rval |> Value.has_type Type.tagged_pointer;
           Objects.is_heap_number lval !mem;
           Objects.is_heap_number rval !mem;
           HeapNumber.is_safe_integer lnum;
           HeapNumber.is_safe_integer rnum;
         ])
  in

  let res =
    Float64.sub lnum.value rnum.value
    |> HeapNumber.from_float64 next_bid (Bool.not deopt_cond) mem
  in

  let wd_value = res in
  let assertion = Value.eq value wd_value in
  (value, Control.empty, assertion, Bool.fl, deopt_cond)

(* simplified: bitwise *)
(* well-defined condition:
 * - WellDefined(pval) ^ IsBool(pval)
 * assertion:
 *  value = ite well-defined (not pval) UB *)
let boolean_not vid pval =
  let value = Value.init vid in
  let deopt_cond = Bool.not (Bool.ands [ Value.has_type Type.bool pval ]) in
  let wd_value = Bool.ite (Value.eq Value.fl pval) Value.tr Value.fl in
  let assertion = Value.eq value wd_value in
  (value, Control.empty, assertion, Bool.fl, deopt_cond)

let speculative_number_bitwise_or vid lval rval next_bid mem =
  let value = Value.init vid in
  let deopt_cond =
    Bool.not
      (Bool.ands
         [
           lval |> Value.has_type Type.tagged_pointer;
           rval |> Value.has_type Type.tagged_pointer;
           Objects.is_heap_number lval !mem;
           Objects.is_heap_number rval !mem;
         ])
  in
  let bitwise_or =
    let lnum = HeapNumber.load lval !mem in
    let rnum = HeapNumber.load rval !mem in
    Value.Int32.or_
      (lnum |> HeapNumber.to_float64 |> Float64.to_int32)
      (rnum |> HeapNumber.to_float64 |> Float64.to_int32)
    |> Value.Int32.to_float64
    |> HeapNumber.from_float64 next_bid (Bool.not deopt_cond) mem
  in

  let assertion = Value.eq value bitwise_or in
  (value, Control.empty, assertion, Bool.fl, deopt_cond)

let speculative_number_bitwise_xor vid lval rval =
  let value = Value.init vid in
  let deopt_cond =
    Bool.not
      (Bool.ands
         [ Value.has_repr Repr.Word32 lval; Value.has_repr Repr.Word32 rval ])
  in
  let wd_value = Value.xor lval rval in
  let assertion = Value.eq value wd_value in
  (value, Control.empty, assertion, Bool.fl, deopt_cond)

(* simplified: comparison *)
let number_less_than vid lval rval next_bid mem =
  let value = Value.init vid in
  let deopt_cond =
    Bool.not
      (Bool.ands
         [
           lval |> Value.has_type Type.tagged_pointer;
           rval |> Value.has_type Type.tagged_pointer;
           Objects.is_heap_number lval !mem;
           Objects.is_heap_number rval !mem;
         ])
  in
  let true_ =
    Float64.one |> HeapNumber.from_float64 next_bid (Bool.not deopt_cond) mem
  in
  let false_ =
    Float64.zero |> HeapNumber.from_float64 next_bid (Bool.not deopt_cond) mem
  in
  let result =
    let lnum = HeapNumber.load lval !mem in
    let rnum = HeapNumber.load rval !mem in
    Bool.ite
      (Bool.ors [ HeapNumber.is_nan lnum; HeapNumber.is_nan rnum ])
      false_
      (Bool.ite
         (Bool.ors
            [
              HeapNumber.eq lnum rnum;
              Bool.ands
                [ HeapNumber.is_zero lnum; HeapNumber.is_minus_zero rnum ];
              Bool.ands
                [ HeapNumber.is_minus_zero lnum; HeapNumber.is_zero rnum ];
            ])
         false_
         (Bool.ite (HeapNumber.is_inf lnum) false_
            (Bool.ite (HeapNumber.is_inf rnum) true_
               (Bool.ite (HeapNumber.is_ninf rnum) false_
                  (Bool.ite (HeapNumber.is_ninf lnum) true_
                     (Bool.ite (HeapNumber.lt lnum rnum) true_ false_))))))
    |> HeapNumber.from_float64 next_bid (Bool.not deopt_cond) mem
  in

  let assertion = Value.eq value result in
  (value, Control.empty, assertion, Bool.fl, deopt_cond)

let speculative_number_equal vid lval rval next_bid mem =
  let value = Value.init vid in
  let deopt_cond =
    Bool.not
      (Bool.ands
         [
           lval |> Value.has_type Type.tagged_pointer;
           rval |> Value.has_type Type.tagged_pointer;
           Objects.is_heap_number lval !mem;
           Objects.is_heap_number rval !mem;
         ])
  in
  let true_ =
    Float64.one |> HeapNumber.from_float64 next_bid (Bool.not deopt_cond) mem
  in
  let false_ =
    Float64.zero |> HeapNumber.from_float64 next_bid (Bool.not deopt_cond) mem
  in
  let result =
    let lnum = HeapNumber.load lval !mem in
    let rnum = HeapNumber.load rval !mem in
    Bool.ite
      (Bool.ors [ HeapNumber.is_nan lnum; HeapNumber.is_nan rnum ])
      false_
      (Bool.ite
         (Bool.ors
            [
              HeapNumber.eq lnum rnum;
              Bool.ands
                [ HeapNumber.is_zero lnum; HeapNumber.is_minus_zero rnum ];
              Bool.ands
                [ HeapNumber.is_minus_zero lnum; HeapNumber.is_zero rnum ];
            ])
         true_ false_)
    |> HeapNumber.from_float64 next_bid (Bool.not deopt_cond) mem
  in

  let assertion = Value.eq value result in
  (value, Control.empty, assertion, Bool.fl, deopt_cond)

(* simplified: memory *)
let allocate_raw vid cid size next_bid ct =
  let value = Value.init vid in
  let control = Control.init cid in
  let pointer = Memory.allocate next_bid size in
  (* assume AllocateRaw doesn't change the control *)
  let assertion = Bool.ands [ Value.eq value pointer; Bool.eq control ct ] in
  (value, control, assertion, Bool.fl, Bool.fl)

let load_element vid tag_value header_size repr bid ind mem =
  let fixed_off = header_size - tag_value in
  let off =
    BitVec.addi
      (BitVec.shli ind (MachineType.Repr.element_size_log2_of repr))
      fixed_off
  in
  Machine.load vid bid off repr mem

let load_field vid tag_value offset repr bid mem =
  let off = offset - tag_value |> BitVecVal.from_int ~len:Value.len in
  Machine.load vid bid off repr mem

let load_typed_element vid array_type base extern ind mem =
  let bid = BitVec.addb base extern in
  let taggedness, header_size, machine_type =
    MachineType.for_type_array_element array_type true
  in
  let repr = MachineType.repr machine_type in
  load_element vid taggedness header_size repr bid ind mem

let store_field ptr pos mt value mem =
  let repr = MachineType.repr mt in

  (* ptr must be pointer type *)
  let ty_check = Value.has_type Type.pointer ptr in

  (* check index out-of-bounds *)
  let can_access = TaggedPointer.can_access_as pos repr ptr in
  let ub_cond = Bool.not (Bool.ands [ ty_check; can_access ]) in
  let store_cond = Bool.not ub_cond in

  mem :=
    Memory.store_as
      (TaggedPointer.move ptr pos |> TaggedPointer.to_raw_pointer)
      repr store_cond value !mem;
  (Value.empty, Control.empty, Bool.tr, ub_cond, Bool.fl)

(* simplified: type-conversion *)
(* well-defined condition
   - IsBool(pval)
   assertion:
    value = ite well-defined (ite pval true false) UB *)
(* [TODO] fix this *)
let change_bit_to_tagged vid pval next_bid mem =
  let value = Value.init vid in
  let deopt_cond = Bool.not (Value.has_type Type.bool pval) in
  let true_ =
    Value.from_f64string "1.0" |> Value.cast Type.float64
    |> HeapNumber.from_float64 next_bid (Bool.not deopt_cond) mem
  in
  let false_ =
    Value.from_f64string "0.0" |> Value.cast Type.float64
    |> HeapNumber.from_float64 next_bid (Bool.not deopt_cond) mem
  in
  let wd_value = Bool.ite (Value.eq Value.tr pval) true_ false_ in
  let assertion = Value.eq value wd_value in
  (value, Control.empty, assertion, Bool.fl, deopt_cond)

(* assertion:
 * value = ite well-defined TaggedSigned(pval) UV *)
let change_int31_to_tagged_signed vid pval =
  let value = Value.init vid in
  let wd_value = Value.Int32.to_tagged_signed pval in
  let assertion = Value.eq value wd_value in
  (value, Control.empty, assertion, Bool.fl, Bool.fl)

(* Assertion =
 *  value = ite well-defined (tagged(pval)) UB *)
let change_int32_to_tagged vid pval next_bid mem =
  let value = Value.init vid in
  let data = Value.data_of pval in

  (* if pval is in smi range, value = TaggedSigned(pval+pval) *)
  let is_in_smi_range = Value.Int32.is_in_smi_range pval in
  let smi = Value.Int32.to_tagged_signed pval in

  let number_value = data |> Float.from_signed_bv |> Float.to_ieee_bv in
  let obj = number_value |> HeapNumber.from_float64 next_bid Bool.tr mem in

  let wd_value = Bool.ite is_in_smi_range smi obj in
  let assertion = Value.eq value wd_value in
  (value, Control.empty, assertion, Bool.fl, Bool.fl)

(* assertion:
 *  value = ite well-defined (tagged(pval)) UB *)
let change_int64_to_tagged vid pval next_bid mem =
  let value = Value.init vid in

  (* if pval is in smi range, value = TaggedSigned(pval+pval) *)
  let is_in_smi_range = Value.Int64.is_in_smi_range pval in
  let smi = Value.Int64.to_tagged_signed pval in

  let number =
    pval |> Value.Int64.to_float64
    |> HeapNumber.from_float64 next_bid is_in_smi_range mem
  in

  let wd_value = Bool.ite is_in_smi_range smi number in
  let assertion = Value.eq value wd_value in
  (value, Control.empty, assertion, Bool.fl, Bool.fl)

let change_tagged_signed_to_int64 vid pval =
  let value = Value.init vid in
  let wd_value = Value.TaggedSigned.to_int64 pval in
  let assertion = Value.eq value wd_value in
  (value, Control.empty, assertion, Bool.fl, Bool.fl)

let change_uint32_to_tagged vid pval next_bid mem =
  let value = Value.init vid in

  let is_in_smi_range = Value.Uint32.is_in_smi_range pval in
  let smi = Value.Uint32.to_tagged_signed pval in
  let number =
    pval |> Value.Uint32.to_float64
    |> HeapNumber.from_float64 next_bid is_in_smi_range mem
  in

  let wd_value = Bool.ite is_in_smi_range smi number in
  let assertion = Value.eq value wd_value in
  (value, Control.empty, assertion, Bool.fl, Bool.fl)

let change_uint64_to_tagged vid pval next_bid mem =
  let value = Value.init vid in

  let is_in_smi_range = Value.Uint64.is_in_smi_range pval in
  let smi = Value.Uint64.to_tagged_signed pval in
  let number =
    pval |> Value.Uint64.to_float64
    |> HeapNumber.from_float64 next_bid is_in_smi_range mem
  in

  let wd_value = Bool.ite is_in_smi_range smi number in
  let assertion = Value.eq value wd_value in
  (value, Control.empty, assertion, Bool.fl, Bool.fl)

(* Deoptimization condition =
 *  LostPrecision(pval)
 *  \/ (hint=CheckForMinusZero /\ pval = -0.0)
 *)
let checked_float64_to_int32 hint vid pval =
  let value = Value.init vid in
  let value32 = pval |> Float64.to_int32 in

  let deopt_cond =
    let lost_precision =
      Bool.not (Float64.eq pval (value32 |> Value.Int32.to_float64))
    in
    let is_minus_zero =
      if hint = "dont-check-for-minus-zero" then Bool.fl
      else if hint = "check-for-minus-zero" then Float64.is_minus_zero pval
      else
        let reason =
          Format.sprintf "CheckedFloat64ToInt32: invalid hint(%s)" hint
        in
        failwith reason
    in
    Bool.ors [ lost_precision; is_minus_zero ]
  in
  let wd_value = value32 in
  let assertion = Value.eq value wd_value in

  (value, Control.empty, assertion, Bool.fl, deopt_cond)

(* Deoptimization condition =
 *  IsNotTaggedSigned(pval)
 * Assertion =
 *  value = ite well-defined Int32(pval >> 1) UV *)
let checked_tagged_signed_to_int32 vid pval =
  let value = Value.init vid in
  let deopt_cond = Bool.not (Value.has_type Type.tagged_signed pval) in
  let wd_value = Value.TaggedSigned.to_int32 pval in
  let assertion = Value.eq value wd_value in
  (value, Control.empty, assertion, Bool.fl, deopt_cond)

let number_to_int32 vid pval next_bid mem =
  let value = Value.init vid in
  let deopt_cond =
    Bool.ands
      [
        pval |> Value.has_type Type.tagged_pointer;
        Objects.is_heap_number pval !mem;
      ]
  in
  (* https://tc39.es/ecma262/#sec-toint32 *)
  let to_int32 =
    let num = HeapNumber.load pval !mem in
    let i = num |> HeapNumber.to_float64 |> Float64.to_int32 in
    i |> Value.Int32.to_float64
    |> HeapNumber.from_float64 next_bid (Bool.not deopt_cond) mem
  in
  let assertion = Value.eq value to_int32 in
  (value, Control.empty, assertion, Bool.fl, deopt_cond)

let speculative_to_number vid pval next_bid mem =
  let value = Value.init vid in
  (* assumption: [pval] is heap number or smi *)
  let deopt_cond =
    Bool.not
      (Bool.ors
         [
           pval |> Value.has_type Type.tagged_signed;
           Bool.ands
             [
               pval |> Value.has_type Type.tagged_pointer;
               Objects.is_heap_number pval !mem;
               HeapNumber.is_safe_integer (HeapNumber.load pval !mem);
             ];
         ])
  in
  let to_number =
    Bool.ite
      (pval |> Value.has_type Type.tagged_signed)
      (Value.TaggedSigned.to_float64 pval)
      (HeapNumber.load pval !mem |> HeapNumber.to_float64)
    |> HeapNumber.from_float64 next_bid (Bool.not deopt_cond) mem
  in
  let assertion = Value.eq value to_number in
  (value, Control.empty, assertion, Bool.fl, deopt_cond)

let to_boolean vid pval mem =
  let value = Value.init vid in
  let uif =
    let value_sort = BV.mk_sort ctx Value.len in
    Z3.FuncDecl.mk_func_decl_s ctx "to_boolean" [ value_sort ] Bool.mk_sort
  in

  let wd_value =
    let number = HeapNumber.load pval !mem in
    Bool.ite
      (Value.has_type Type.tagged_signed pval)
      (* smi *)
      (Bool.ite (Value.TaggedSigned.is_zero pval) Value.fl Value.tr)
      (Bool.ite
         (Objects.is_heap_number pval !mem)
         (* heap number *)
         (Bool.ite
            (Bool.ors
               [
                 HeapNumber.is_minus_zero number;
                 HeapNumber.is_zero number;
                 HeapNumber.is_nan number;
               ])
            Value.fl Value.tr)
         (* currently only handle the number;
            look: https://tc39.es/ecma262/#sec-toboolean *)
         (Bool.ite (Z3.FuncDecl.apply uif [ pval ]) Value.tr Value.fl))
  in
  let assertion = Value.eq value wd_value in
  (value, Control.empty, assertion, Bool.fl, Bool.fl)

let truncate_tagged_to_bit vid pval mem =
  let value = Value.init vid in
  let uif =
    let value_sort = BV.mk_sort ctx Value.len in
    Z3.FuncDecl.mk_func_decl_s ctx "truncate_tagged_to_bit" [ value_sort ]
      Bool.mk_sort
  in

  let res =
    let number = HeapNumber.load pval !mem in
    Bool.ite
      (* if [pval] is smi, return [pval] != 0 *)
      (pval |> Value.has_type Type.tagged_signed)
      (Bool.ite (Value.TaggedSigned.is_zero pval) Value.fl Value.tr)
      (Bool.ite
         (* if [pval] is heap number, return [pval] != 0.0, -0.0 or NaN *)
         (Bool.ands
            [
              pval |> Value.has_type Type.tagged_pointer;
              Objects.is_heap_number pval !mem;
            ])
         (Bool.ite
            (Bool.ors
               [
                 HeapNumber.is_minus_zero number;
                 HeapNumber.is_zero number;
                 HeapNumber.is_nan number;
               ])
            Value.fl Value.tr)
         (* otherwise, pass it to uif
            [TODO] handle other objects
            (look: LowerTruncateTaggedToBit@src/compiler/effect-control-linearizer.cc) *)
         (Bool.ite (Z3.FuncDecl.apply uif [ pval ]) Value.tr Value.fl))
  in

  let assertion = Value.eq value res in
  (value, Control.empty, assertion, Bool.fl, Bool.fl)
