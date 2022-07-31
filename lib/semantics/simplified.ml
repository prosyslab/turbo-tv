open Z3utils
module HeapNumber = Objects.HeapNumber
module Repr = MachineType.Repr

(* helper functions *)
let check_map_for_heap_number_or_oddball_to_float64 hint pval mem =
  let is_heap_number = pval |> Objects.is_heap_number mem in
  let is_boolean = pval |> Objects.is_boolean mem in
  match hint with
  | "Number" -> is_heap_number
  | "NumberOrBoolean" -> Bool.ors [ is_heap_number; is_boolean ]
  (* TODO: Implement MapInstanceType for NumberOrOddball *)
  | "NumberOrOddball" -> Bool.tr
  | _ ->
      failwith (Printf.sprintf "CheckedTaggedToFloat64: Undefined hint %s" hint)

(* simplified: numeric *)
let number_abs nptr next_bid mem state =
  let deopt =
    Bool.not
      (Bool.ands
         [
           nptr |> Value.has_type Type.tagged_pointer;
           nptr |> Objects.is_heap_number mem;
         ])
  in
  (* https://tc39.es/ecma262/#sec-math.abs *)
  let value, next_bid, mem =
    let n = HeapNumber.load nptr mem in
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
    |> HeapNumber.from_float64 next_bid (Bool.not deopt) mem
  in
  state |> State.update ~value ~deopt ~next_bid ~mem

let number_add lval rval mem state =
  let value = Number.add lval rval mem in
  state |> State.update ~value

let number_ceil pval mem state =
  let value = pval |> Number.ceil mem in
  state |> State.update ~value

let number_divide lval rval mem state =
  let value = Number.divide lval rval mem in
  state |> State.update ~value

let number_expm1 nptr next_bid mem state =
  let deopt =
    Bool.not
      (Bool.ands
         [
           nptr |> Value.has_type Type.tagged_pointer;
           nptr |> Objects.is_heap_number mem;
         ])
  in
  (* https://tc39.es/ecma262/#sec-math.expm1 *)
  let value, next_bid, mem =
    let num = HeapNumber.load nptr mem in
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
         (Float64.from_numeral (-1.0))
         (Z3.FuncDecl.apply expm_decl [ num.value ] |> Value.entype Type.float64))
    |> HeapNumber.from_float64 next_bid (Bool.not deopt) mem
  in
  state |> State.update ~value ~deopt ~next_bid ~mem

let number_floor pval mem state =
  let value = pval |> Number.floor mem in
  state |> State.update ~value

let number_imul lval rval mem state =
  let value = Number.imul lval rval mem in
  state |> State.update ~value

let number_max lval rval next_bid mem state =
  let deopt =
    Bool.not
      (Bool.ands
         [
           lval |> Value.has_type Type.tagged_pointer;
           rval |> Value.has_type Type.tagged_pointer;
           lval |> Objects.is_heap_number mem;
           rval |> Objects.is_heap_number mem;
         ])
  in
  (* https://tc39.es/ecma262/#sec-math.max *)
  let value, next_bid, mem =
    let lnum = HeapNumber.load lval mem in
    let rnum = HeapNumber.load rval mem in
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
    |> HeapNumber.from_float64 next_bid (Bool.not deopt) mem
  in
  state |> State.update ~value ~deopt ~next_bid ~mem

let number_min lval rval next_bid mem state =
  let deopt =
    Bool.not
      (Bool.ands
         [
           lval |> Value.has_type Type.tagged_pointer;
           rval |> Value.has_type Type.tagged_pointer;
           lval |> Objects.is_heap_number mem;
           rval |> Objects.is_heap_number mem;
         ])
  in
  (* https://tc39.es/ecma262/#sec-math.min *)
  let value, next_bid, mem =
    let lnum = HeapNumber.load lval mem in
    let rnum = HeapNumber.load rval mem in
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
    |> HeapNumber.from_float64 next_bid (Bool.not deopt) mem
  in
  state |> State.update ~value ~deopt ~next_bid ~mem

let number_modulus lval rval mem state =
  let value = Number.remainder lval rval mem in
  state |> State.update ~value

let number_multiply lval rval next_bid mem state =
  let value = Number.multiply lval rval mem in
  state |> State.update ~value ~next_bid ~mem

let number_round pval mem state =
  let value = pval |> Number.round mem in
  state |> State.update ~value

let number_sign pval mem state =
  let value = pval |> Number.sign mem in
  state |> State.update ~value

let number_sin pval mem state =
  let value = pval |> Number.sin mem in
  state |> State.update ~value

let number_subtract lval rval mem state =
  let value = Number.subtract lval rval mem in
  state |> State.update ~value

let number_trunc pval mem state =
  let value = Number.trunc pval mem in
  state |> State.update ~value

(* deopt condition: not(IsNumber(lval) /\ IsNumber(rval))
 * value: Float64(lval + rval) *)
let speculative_number_add lval rval mem state =
  let deopt = Bool.not (Number.are_numbers [ lval; rval ] mem) in
  state |> number_add lval rval mem |> State.update ~deopt

(* deopt condition: not(IsNumber(lval) /\ IsNumber(rval))
 * value: Float64(lval / rval) *)
let speculative_number_divide lval rval _eff control mem state =
  let deopt = Bool.not (Number.are_numbers [ lval; rval ] mem) in
  state |> number_divide lval rval mem |> State.update ~deopt ~control

(* deopt condition: not(IsNumber(lval) /\ IsNumber(rval))
 * value: Float64(lval x rval) *)
let speculative_number_modulus lval rval _eff control mem state =
  let deopt = Bool.not (Number.are_numbers [ lval; rval ] mem) in
  state |> number_modulus lval rval mem |> State.update ~deopt ~control

(* deopt condition: not(IsNumber(lval) /\ IsNumber(rval))
 * value: Float64(lval x rval) *)
let speculative_number_multiply lval rval next_bid mem state =
  let deopt = Bool.not (Number.are_numbers [ lval; rval ] mem) in
  state |> number_multiply lval rval next_bid mem |> State.update ~deopt

(* deopt condition: not(IsNumber(lval) /\ IsNumber(rval))
 * value: Float64(lval - rval) *)
let speculative_number_subtract lval rval _effect control mem state =
  let deopt = Bool.not (Number.are_numbers [ lval; rval ] mem) in
  state |> number_subtract lval rval mem |> State.update ~deopt ~control

(* well-defined condition:
 * (IsTaggedSigned(lval) /\ IsTaggedSigned(rval))
 * \/ (IsTaggedPointer(lval) /\ IsTaggedPointer(rval)
 *    /\ PointsNumberObject(lval) /\ PointsNumberObject(rval)
 *    /\ IsAdditiveSafeInteger(lval) /\ IsAdditiveSafeInteger(rval))
 * assertion:
 *  value = ite well-defined (lval+rval) UB *)
let speculative_safe_integer_add lval rval next_bid mem state =
  let deopt =
    let is_safe_integer value =
      Bool.ors
        [
          value |> Value.has_type Type.tagged_signed;
          Bool.ands
            [
              value |> Value.has_type Type.tagged_pointer;
              value |> Objects.is_heap_number mem;
              HeapNumber.is_safe_integer (HeapNumber.load value mem);
            ];
        ]
    in
    Bool.not (Bool.ands [ is_safe_integer lval; is_safe_integer rval ])
  in
  let added_f64 =
    let value_to_float64 value =
      let number = HeapNumber.load value mem in
      Bool.ite
        (value |> Value.has_type Type.tagged_signed)
        (Value.TaggedSigned.to_float64 value)
        (number.value |> Value.entype Type.float64)
    in
    let lf = lval |> value_to_float64 in
    let rf = rval |> value_to_float64 in
    Float64.add lf rf
  in
  let value, next_bid, mem =
    added_f64 |> HeapNumber.from_float64 next_bid (Bool.not deopt) mem
  in
  state |> State.update ~value ~deopt ~next_bid ~mem

(* deopt condition: not(IsNumber(lval) /\ IsNumber(rval))
 * value: Float64(lval - rval) *)
let speculative_safe_integer_subtract lval rval next_bid mem state =
  let lnum = HeapNumber.load lval mem in
  let rnum = HeapNumber.load rval mem in
  let deopt =
    Bool.not
      (Bool.ands
         [
           lval |> Value.has_type Type.tagged_pointer;
           rval |> Value.has_type Type.tagged_pointer;
           lval |> Objects.is_heap_number mem;
           rval |> Objects.is_heap_number mem;
           HeapNumber.is_safe_integer lnum;
           HeapNumber.is_safe_integer rnum;
         ])
  in
  let value, next_bid, mem =
    Float64.sub lnum.value rnum.value
    |> HeapNumber.from_float64 next_bid (Bool.not deopt) mem
  in
  state |> State.update ~value ~deopt ~next_bid ~mem

(* simplified: bitwise *)
(* well-defined condition:
 * - WellDefined(pval) ^ IsBool(pval)
 * assertion:
 *  value = ite well-defined (not pval) UB *)
let boolean_not pval state =
  let deopt = Bool.not (Bool.ands [ Value.has_type Type.bool pval ]) in
  let value = Bool.ite (Value.eq Value.fl pval) Value.tr Value.fl in
  state |> State.update ~value ~deopt

(* 2V -> 1V *)
let number_shift_right_logical lval rval mem state =
  let value = Number.unsigned_right_shift lval rval mem in
  state |> State.update ~value

let speculative_number_bitwise_or lval rval next_bid mem state =
  let deopt = Bool.not (Number.are_numbers [ lval; rval ] mem) in
  let value, next_bid, mem =
    let lnum = HeapNumber.load lval mem in
    let rnum = HeapNumber.load rval mem in
    Value.Int32.or_
      (lnum |> HeapNumber.to_float64 |> Float64.to_int32)
      (rnum |> HeapNumber.to_float64 |> Float64.to_int32)
    |> Value.Int32.to_float64
    |> HeapNumber.from_float64 next_bid (Bool.not deopt) mem
  in
  state |> State.update ~value ~deopt ~next_bid ~mem

let speculative_number_bitwise_xor lval rval state =
  let deopt =
    Bool.not
      (Bool.ands
         [ Value.has_repr Repr.Word32 lval; Value.has_repr Repr.Word32 rval ])
  in
  let value = Value.xor lval rval in

  state |> State.update ~value ~deopt

(* 2V1E1C -> 1V *)
let speculative_number_shift_right_logical lval rval _eff control mem state =
  let deopt = Bool.not (Number.are_numbers [ lval; rval ] mem) in
  state
  |> number_shift_right_logical lval rval mem
  |> State.update ~control ~deopt

(* simplified: comparison *)
let number_equal lnum rnum mem state =
  let value = Number.equal lnum rnum mem in
  state |> State.update ~value

let number_less_than lnum rnum mem state =
  let value =
    Bool.ite (Value.is_true (Number.less_than lnum rnum mem)) Value.tr Value.fl
  in
  state |> State.update ~value

let number_less_than_or_equal lnum rnum mem state =
  (* https://tc39.es/ecma262/#sec-relational-operators-runtime-semantics-evaluation *)
  let value =
    let r = Number.less_than rnum lnum mem in
    Bool.ite
      (Bool.ors [ r |> Value.is_true; r |> Value.is_undefined ])
      Value.fl Value.tr
  in
  state |> State.update ~value

let object_is_nan pval mem state =
  let value =
    let is_smi = Value.has_type Type.tagged_signed pval in
    Bool.ite is_smi Value.fl
      (let is_heap_number = Objects.is_heap_number mem pval in
       Bool.ite is_heap_number
         (let number = HeapNumber.load pval mem in
          HeapNumber.is_nan number)
         Value.fl)
  in
  state |> State.update ~value

let speculative_number_equal lval rval mem state =
  let deopt = Bool.not (Number.are_numbers [ lval; rval ] mem) in
  state |> number_equal lval rval mem |> State.update ~deopt

let speculative_number_less_than lval rval _eff control mem state =
  let deopt = Bool.not (Number.are_numbers [ lval; rval ] mem) in
  state |> number_less_than lval rval mem |> State.update ~deopt ~control

let speculative_number_less_than_or_equal lval rval _eff control mem state =
  let deopt = Bool.not (Number.are_numbers [ lval; rval ] mem) in
  state
  |> number_less_than_or_equal lval rval mem
  |> State.update ~deopt ~control

(* simplified: memory *)
let allocate_raw size control state =
  let bid = State.next_bid state in
  let next_bid, value = Memory.allocate bid size in
  (* assume AllocateRaw doesn't change the control *)
  state |> State.update ~value ~control ~next_bid

let load_element tag_value header_size repr bid ind mem state =
  let fixed_off = header_size - tag_value in
  let off =
    BitVec.addi
      (BitVec.shli ind (MachineType.Repr.element_size_log2_of repr))
      fixed_off
  in
  state |> Machine.load bid off repr mem

let load_field tag_value offset repr bid mem state =
  let off = offset - tag_value |> BitVecVal.from_int ~len:Value.len in
  state |> Machine.load bid off repr mem

let load_typed_element array_type base extern ind mem state =
  let bid = BitVec.addb base extern in
  let taggedness, header_size, machine_type =
    MachineType.for_type_array_element array_type true
  in
  let repr = MachineType.repr machine_type in
  state |> load_element taggedness header_size repr bid ind mem

(* V2E1C1 -> E1 *)
let store_element tag_value header_size repr bid ind value mem control state =
  let fixed_off = header_size - tag_value in
  let off =
    BitVec.addi
      (BitVec.shli ind (MachineType.Repr.element_size_log2_of repr))
      fixed_off
  in
  state |> Machine.store bid off repr value mem |> State.update ~control

let store_field ptr pos mt value mem state =
  let repr = MachineType.repr mt in

  (* ptr must be pointer type *)
  let ty_check = Value.has_type Type.tagged_pointer ptr in

  (* check index out-of-bounds *)
  let can_access = TaggedPointer.can_access_as pos repr ptr in
  let _ub = Bool.not (Bool.ands [ ty_check; can_access ]) in
  let store_cond = Bool.not _ub in

  let mem =
    mem
    |> Memory.store_as
         (TaggedPointer.move ptr pos |> TaggedPointer.to_raw_pointer)
         repr store_cond value
  in
  state |> State.update ~mem

(* simplified: type-conversion *)
(* well-defined condition
   - IsBool(pval)
   assertion:
    value = ite well-defined (ite pval true false) UB *)
(* [TODO] fix this *)
let change_bit_to_tagged pval next_bid mem state =
  let deopt = Bool.not (Value.has_type Type.bool pval) in
  let true_, next_bid, mem =
    Value.from_f64string "1.0" |> Value.cast Type.float64
    |> HeapNumber.from_float64 next_bid (Bool.not deopt) mem
  in
  let false_, next_bid, mem =
    Value.from_f64string "0.0" |> Value.cast Type.float64
    |> HeapNumber.from_float64 next_bid (Bool.not deopt) mem
  in
  let value = Bool.ite (Value.eq Value.tr pval) true_ false_ in

  state |> State.update ~value ~deopt ~next_bid ~mem

(* assertion:
 * value = ite well-defined TaggedSigned(pval) UV *)
let change_int31_to_tagged_signed pval state =
  let value = Value.Int32.to_tagged_signed pval in

  state |> State.update ~value

(* Assertion =
 *  value = ite well-defined (tagged(pval)) UB *)
let change_int32_to_tagged pval next_bid mem state =
  let data = Value.data_of pval in

  (* if pval is in smi range, value = TaggedSigned(pval+pval) *)
  let is_in_smi_range = Value.Int32.is_in_smi_range pval in
  let smi = Value.Int32.to_tagged_signed pval in

  let number_value = data |> Float.from_signed_bv |> Float.to_ieee_bv in
  let obj, next_bid, mem =
    number_value |> HeapNumber.from_float64 next_bid Bool.tr mem
  in

  let value = Bool.ite is_in_smi_range smi obj in

  state |> State.update ~value ~next_bid ~mem

(* assertion:
 *  value = ite well-defined (tagged(pval)) UB *)
let change_int64_to_tagged pval next_bid mem state =
  (* if pval is in smi range, value = TaggedSigned(pval+pval) *)
  let is_in_smi_range = Value.Int64.is_in_smi_range pval in
  let smi = Value.Int64.to_tagged_signed pval in

  let number, next_bid, mem =
    pval |> Value.Int64.to_float64
    |> HeapNumber.from_float64 next_bid is_in_smi_range mem
  in

  let value = Bool.ite is_in_smi_range smi number in

  state |> State.update ~value ~next_bid ~mem

let change_tagged_signed_to_int64 pval state =
  let value = Value.TaggedSigned.to_int64 pval in
  state |> State.update ~value

let change_uint32_to_tagged pval next_bid mem state =
  let is_in_smi_range = Value.Uint32.is_in_smi_range pval in
  let smi = Value.Uint32.to_tagged_signed pval in
  let number, next_bid, mem =
    pval |> Value.Uint32.to_float64
    |> HeapNumber.from_float64 next_bid (Bool.not is_in_smi_range) mem
  in

  let value = Bool.ite is_in_smi_range smi number in

  state |> State.update ~value ~next_bid ~mem

let change_uint64_to_tagged pval next_bid mem state =
  let is_in_smi_range = Value.Uint64.is_in_smi_range pval in
  let smi = Value.Uint64.to_tagged_signed pval in
  let number, next_bid, mem =
    pval |> Value.Uint64.to_float64
    |> HeapNumber.from_float64 next_bid (Bool.not is_in_smi_range) mem
  in
  let value = Bool.ite is_in_smi_range smi number in
  state |> State.update ~value ~next_bid ~mem

(* Deoptimization condition =
 *  LostPrecision(pval)
 *  \/ (hint=CheckForMinusZero /\ pval = -0.0)
 *)
let checked_float64_to_int32 hint pval state =
  let value32 = pval |> Float64.to_int32 in

  let deopt =
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
  let value = value32 in
  state |> State.update ~value ~deopt

(* Deoptimization condition =
 *  LostPrecision(pval) *)
let checked_int64_to_int32 pval _mem control state =
  let value = pval |> Value.Int64.to_int32 in
  let deopt =
    (* lost-precision *)
    Bool.not (Value.eq pval (value |> Value.Int32.to_int64))
  in
  state |> State.update ~value ~control ~deopt

(* Deoptimization condition =
 *  IsNotTaggedSigned(pval)
 * Assertion =
 *  value = ite well-defined Int32(pval >> 1) UV *)
let checked_tagged_signed_to_int32 pval state =
  let deopt = Bool.not (Value.has_type Type.tagged_signed pval) in
  let value = Value.TaggedSigned.to_int32 pval in
  state |> State.update ~value ~deopt

let checked_tagged_to_float64 hint pval mem state =
  let is_tagged_signed = pval |> Value.has_type Type.tagged_signed in
  let is_tagged_pointer = pval |> Value.has_type Type.tagged_pointer in
  let map_check =
    check_map_for_heap_number_or_oddball_to_float64 hint pval mem
  in
  let deopt = Bool.ands [ is_tagged_pointer; Bool.not map_check ] in
  let value =
    Bool.ite is_tagged_signed
      (Value.TaggedSigned.to_float64 pval)
      (HeapNumber.load pval mem |> HeapNumber.to_float64)
  in
  state |> State.update ~value ~deopt

let checked_tagged_to_tagged_pointer pval _checkpoint control state =
  let deopt_cond =
    Bool.ite (pval |> Value.has_type Type.tagged_signed) Value.tr Value.fl
  in
  state |> Common.deoptimize_if deopt_cond () () control

let checked_tagged_to_tagged_signed pval state =
  let deopt =
    Bool.ite (pval |> Value.has_type Type.tagged_signed) Value.fl Value.tr
  in
  state |> State.update ~value:pval ~deopt

let checked_truncate_tagged_to_word32 hint pval mem state =
  let is_tagged_signed = pval |> Value.has_type Type.tagged_signed in
  let is_tagged_pointer = pval |> Value.has_type Type.tagged_pointer in
  let map_check =
    check_map_for_heap_number_or_oddball_to_float64 hint pval mem
  in
  let deopt = Bool.ands [ is_tagged_pointer; Bool.not map_check ] in
  let value =
    Bool.ite is_tagged_signed
      (Value.TaggedSigned.to_int32 pval)
      (HeapNumber.load pval mem |> HeapNumber.to_float64 |> Float64.to_int32)
  in
  state |> State.update ~value ~deopt

let number_to_int32 pval next_bid mem state =
  let deopt =
    Bool.ands
      [
        pval |> Value.has_type Type.tagged_pointer;
        pval |> Objects.is_heap_number mem;
      ]
  in
  (* https://tc39.es/ecma262/#sec-toint32 *)
  let value, next_bid, mem =
    let num = HeapNumber.load pval mem in
    let i = num |> HeapNumber.to_float64 |> Float64.to_int32 in
    i |> Value.Int32.to_float64
    |> HeapNumber.from_float64 next_bid (Bool.not deopt) mem
  in
  state |> State.update ~value ~deopt ~next_bid ~mem

(* pure: 1V -> 1V *)
let number_to_uint32 pval mem state =
  let value = pval |> Number.to_uint32 mem in
  state |> State.update ~value

let speculative_to_number pval next_bid mem state =
  (* assumption: [pval] is heap number or smi *)
  let deopt =
    Bool.not
      (Bool.ors
         [
           pval |> Value.has_type Type.tagged_signed;
           Bool.ands
             [
               pval |> Value.has_type Type.tagged_pointer;
               pval |> Objects.is_heap_number mem;
             ];
         ])
  in
  let value, next_bid, mem =
    Bool.ite
      (pval |> Value.has_type Type.tagged_signed)
      (Value.TaggedSigned.to_float64 pval)
      (HeapNumber.load pval mem |> HeapNumber.to_float64)
    |> HeapNumber.from_float64 next_bid (Bool.not deopt) mem
  in
  state |> State.update ~value ~deopt ~next_bid ~mem

let to_boolean pval mem state =
  let uif =
    let value_sort = BV.mk_sort ctx Value.len in
    Z3.FuncDecl.mk_func_decl_s ctx "to_boolean" [ value_sort ] Bool.mk_sort
  in

  let value =
    let number = HeapNumber.load pval mem in
    Bool.ite
      (* smi *)
      (Value.has_type Type.tagged_signed pval)
      (Bool.ite (Value.TaggedSigned.is_zero pval) Value.fl Value.tr)
      (Bool.ite
         (* heap number *)
         (pval |> Objects.is_heap_number mem)
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

  state |> State.update ~value

let truncate_tagged_to_bit pval mem state =
  let uif =
    let value_sort = BV.mk_sort ctx Value.len in
    Z3.FuncDecl.mk_func_decl_s ctx "truncate_tagged_to_bit" [ value_sort ]
      Bool.mk_sort
  in
  let value =
    let number = HeapNumber.load pval mem in
    Bool.ite
      (* if [pval] is smi, return [pval] != 0 *)
      (pval |> Value.has_type Type.tagged_signed)
      (Bool.ite (Value.TaggedSigned.is_zero pval) Value.fl Value.tr)
      (Bool.ite
         (* if [pval] is heap number, return [pval] != 0.0, -0.0 or NaN *)
         (Bool.ands
            [
              pval |> Value.has_type Type.tagged_pointer;
              pval |> Objects.is_heap_number mem;
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
  state |> State.update ~value
