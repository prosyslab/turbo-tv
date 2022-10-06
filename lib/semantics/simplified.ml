open Z3utils
open ValueOperator
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
  | "NumberOrOddball" -> Bool.fl
  | _ ->
      failwith (Printf.sprintf "CheckedTaggedToFloat64: Undefined hint %s" hint)

(* simplified: numeric *)
let checked_int32_add lval rval _eff control state =
  let deopt = Int32.add_would_overflow lval rval in
  state |> Machine.int32_add lval rval |> State.update ~deopt ~control

let checked_int32_div lval rval _eff control state =
  let deopt =
    let division_by_zero = Int32.is_zero rval in
    let minus_zero = Bool.ands [ Int32.is_zero lval; Int32.is_negative rval ] in
    let overflow =
      Bool.ands
        [ Int32.eq Int32.min_limit lval; Int32.eq rval (Value.from_int (-1)) ]
    in
    let lost_precision =
      Bool.not (Int32.eq (Int32.srem lval rval) Int32.zero)
    in
    Bool.ors [ division_by_zero; minus_zero; overflow; lost_precision ]
  in
  state |> Machine.int32_div lval rval control |> State.update ~deopt ~control

let checked_int32_mul mode lval rval _eff control state =
  let deopt =
    let check_overflow = Int32.mul_would_overflow lval rval in
    let check_minus_zero =
      if mode = "check-for-minus-zero" then
        let mul_is_zero = Int32.mul lval rval |> Int32.is_zero in
        let one_is_negative =
          Bool.ors [ Int32.is_negative lval; Int32.is_negative rval ]
        in
        Bool.ands [ mul_is_zero; one_is_negative ]
      else Bool.fl
    in
    Bool.ors [ check_overflow; check_minus_zero ]
  in
  state |> Machine.int32_mul lval rval |> State.update ~deopt ~control

let checked_int32_sub lval rval _eff control state =
  let deopt = Int32.sub_would_overflow lval rval in
  state |> Machine.int32_sub lval rval |> State.update ~deopt ~control

let checked_uint32_div lval rval _eff control state =
  let deopt =
    let division_by_zero = Uint32.is_zero rval in
    let lost_precision =
      Bool.not (Uint32.eq (Uint32.urem lval rval) Uint32.zero)
    in
    Bool.ors [ division_by_zero; lost_precision ]
  in
  state |> Machine.uint32_div lval rval control |> State.update ~deopt ~control

let number_abs nptr mem state =
  let value = nptr |> Number.abs mem in
  state |> State.update ~value

let number_add lval rval mem state =
  let value = Number.add lval rval mem in
  state |> State.update ~value

let number_ceil pval mem state =
  let value = pval |> Number.ceil mem in
  state |> State.update ~value

let number_divide lval rval mem state =
  let value = Number.divide lval rval mem in
  state |> State.update ~value

let number_expm1 pval mem state =
  (* https://tc39.es/ecma262/#sec-math.expm1 *)
  let value = pval |> Number.expm1 mem in
  state |> State.update ~value

let number_floor pval mem state =
  let value = pval |> Number.floor mem in
  state |> State.update ~value

let number_imul lval rval mem state =
  let value =
    let res = Number.imul lval rval mem in
    Bool.ite
      (res |> Int32.is_in_smi_range)
      (res |> Int32.to_tagged_signed)
      (res |> Int32.to_float64)
  in
  state |> State.update ~value

let number_max lval rval mem state =
  let value = Number.max lval rval mem in
  state |> State.update ~value ~mem

let number_min lval rval mem state =
  let value = Number.min lval rval mem in
  state |> State.update ~value ~mem

let number_modulus lval rval mem state =
  let value = Number.remainder lval rval mem in
  state |> State.update ~value

let number_multiply lval rval mem state =
  let value = Number.multiply lval rval mem in
  state |> State.update ~value ~mem

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
let speculative_number_multiply lval rval _eff control mem state =
  let deopt = Bool.not (Number.are_numbers [ lval; rval ] mem) in
  state |> number_multiply lval rval mem |> State.update ~deopt ~control

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
let speculative_safe_integer_add lval rval control mem state =
  let res = Number.add lval rval mem in
  let deopt =
    Bool.not
      (Bool.ands
         [
           Number.are_numbers [ lval; rval ] mem;
           Number.are_safe_integer [ lval; rval; res ] mem;
         ])
  in
  let value = res in
  state |> State.update ~value ~deopt ~control

(* deopt condition: not(IsNumber(lval) /\ IsNumber(rval))
 * value: Float64(lval - rval) *)
let speculative_safe_integer_subtract lval rval control mem state =
  let res = Number.subtract lval rval mem in
  let deopt =
    Bool.not
      (Bool.ands
         [
           Number.are_numbers [ lval; rval ] mem;
           Number.are_safe_integer [ lval; rval; res ] mem;
         ])
  in
  let value = res in
  state |> State.update ~value ~deopt ~control

(* simplified: bitwise *)
(* well-defined condition:
 * - WellDefined(pval) ^ IsBool(pval)
 * assertion:
 *  value = ite well-defined (not pval) UB *)
let boolean_not pval state =
  let value = Bool.ite (Value.eq Value.fl pval) Value.tr Value.fl in
  state |> State.update ~value

(* 2V -> 1V *)
let number_shift_left lval rval mem state =
  let value = Number.left_shift lval rval mem in
  state |> State.update ~value

let number_shift_right lval rval mem state =
  let value = Number.signed_right_shfit lval rval mem in
  state |> State.update ~value

let number_shift_right_logical lval rval mem state =
  let value = Number.unsigned_right_shift lval rval mem in
  state |> State.update ~value

let number_bitwise op lval rval mem state =
  let value = Number.bitwise op lval rval mem in
  state |> State.update ~value

let speculative_number_bitwise op lval rval mem state =
  let deopt = Bool.not (Number.are_numbers [ lval; rval ] mem) in
  state |> number_bitwise op lval rval mem |> State.update ~deopt

let speculative_number_shift_left lval rval _eff control mem state =
  let deopt = Bool.not (Number.are_numbers [ lval; rval ] mem) in
  state |> number_shift_left lval rval mem |> State.update ~control ~deopt

let speculative_number_shift_right lval rval _eff control mem state =
  let deopt = Bool.not (Number.are_numbers [ lval; rval ] mem) in
  state |> number_shift_right lval rval mem |> State.update ~control ~deopt

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

let number_same_value lnum rnum mem state =
  let rf = State.register_file state in
  let true_cst = RegisterFile.find "true" rf in
  let false_cst = RegisterFile.find "false" rf in
  let value = Bool.ite (Number.same_value lnum rnum mem) true_cst false_cst in
  state |> State.update ~value

let same_value lval rval mem state =
  (* when non-number type values are given, set deopt flag to avoid mis-verification *)
  let deopt = Bool.not (Number.are_numbers [ lval; rval ] mem) in
  state |> number_same_value lval rval mem |> State.update ~deopt

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
let allocate_raw size control mem state =
  let ptr, mem = Memory.allocate size mem in
  state |> State.update ~value:ptr ~control ~mem

let load_element tag_value header_size repr bid ind mem state =
  let fixed_off = header_size - tag_value in
  let off =
    BitVec.addi
      (BitVec.shli ind (MachineType.Repr.element_size_log2_of repr))
      fixed_off
  in
  state |> Machine.load bid off repr mem

let load_field _tag_value offset repr ptr _eff control mem state =
  let off = offset |> BitVecVal.from_int ~len:Value.len in
  state |> Machine.load ptr off repr mem |> State.update ~control

let load_typed_element array_type base extern ind mem state =
  let bid = BitVec.addb base extern in
  let taggedness, header_size, machine_type =
    MachineType.for_type_array_element array_type true
  in
  let repr = MachineType.repr machine_type in
  state |> load_element taggedness header_size repr bid ind mem

(* V2E1C1 -> E1 *)
let store_element _tag_value header_size repr bid ind value mem control state =
  let fixed_off = header_size in
  let off =
    BitVec.addi
      (BitVec.shli ind (MachineType.Repr.element_size_log2_of repr))
      fixed_off
  in
  state |> Machine.store bid off repr value mem |> State.update ~control

let store_field ptr off repr value _eff control mem state =
  let off = off |> BitVecVal.from_int ~len:Value.len in
  state |> Machine.store ptr off repr value mem |> State.update ~control

(* simplified: type-check *)
let number_is_minus_zero pval mem state =
  let value = Bool.ite (pval |> Number.is_minus_zero mem) Value.tr Value.fl in
  state |> State.update ~value

let number_is_nan pval mem state =
  let value = Bool.ite (pval |> Number.is_nan mem) Value.tr Value.fl in
  state |> State.update ~value

let object_is_minus_zero pval mem state =
  (* when non-number type values are given, set deopt flag to avoid mis-verification *)
  let deopt = Bool.not (Number.is_number pval mem) in
  let rf = State.register_file state in
  let true_constant = RegisterFile.find "true" rf in
  let false_constant = RegisterFile.find "false" rf in
  let value =
    Bool.ite (pval |> Number.is_minus_zero mem) true_constant false_constant
  in
  state |> State.update ~value ~deopt

let object_is_nan pval mem state =
  (* when non-number type values are given, set deopt flag to avoid mis-verification *)
  let deopt = Bool.not (Number.is_number pval mem) in
  let rf = State.register_file state in
  let true_constant = RegisterFile.find "true" rf in
  let false_constant = RegisterFile.find "false" rf in
  let value =
    Bool.ite (pval |> Number.is_nan mem) true_constant false_constant
  in
  state |> State.update ~value ~deopt

(* simplified: type-conversion *)
(* well-defined condition
   - IsBool(pval)
   assertion:
    value = ite well-defined (ite pval true false) UB *)
let change_bit_to_tagged pval state =
  let rf = State.register_file state in
  let true_constant = RegisterFile.find "true" rf in
  let false_constant = RegisterFile.find "false" rf in
  let value = Bool.ite (Value.eq Value.tr pval) true_constant false_constant in
  state |> State.update ~value

let change_float64_to_tagged mode pval mem state =
  let smi_cond =
    if mode = "check-for-minus-zero" then
      Bool.ands
        [ pval |> Float64.can_be_smi; Bool.not (pval |> Float64.is_minus_zero) ]
    else pval |> Float64.can_be_smi
  in
  let smi = pval |> Float64.to_tagged_signed in
  let heap_number = pval in
  let value = Bool.ite smi_cond smi heap_number in
  state |> State.update ~value ~mem

(* assertion:
 * value = ite well-defined TaggedSigned(pval) UV *)
let change_int31_to_tagged_signed pval state =
  let value = Int32.to_tagged_signed pval in
  state |> State.update ~value

(* Assertion =
 *  value = ite well-defined (tagged(pval)) UB *)
let change_int32_to_tagged pval state =
  let is_in_smi_range = pval |> Int32.is_in_smi_range in
  let smi = pval |> Int32.to_tagged_signed in
  let heap_number = pval |> Int32.to_float64 in
  let value = Bool.ite is_in_smi_range smi heap_number in
  state |> State.update ~value

(* assertion:
 *  value = ite well-defined (tagged(pval)) UB *)
let change_int64_to_tagged pval state =
  (* if pval is in smi range, value = TaggedSigned(pval+pval) *)
  let is_in_smi_range = Int64.is_in_smi_range pval in
  let smi = pval |> Int64.to_tagged_signed in
  let heap_number = pval |> Int64.to_float64 in
  let value = Bool.ite is_in_smi_range smi heap_number in
  state |> State.update ~value

let change_tagged_signed_to_int64 pval state =
  let value = TaggedSigned.to_int64 pval in
  state |> State.update ~value

let change_uint32_to_tagged pval state =
  let is_in_smi_range = Uint32.is_in_smi_range pval in
  let smi = Uint32.to_tagged_signed pval in
  let heap_number = Uint32.to_float64 pval in
  let value = Bool.ite is_in_smi_range smi heap_number in
  state |> State.update ~value

let change_uint64_to_tagged pval state =
  let is_in_smi_range = Uint64.is_in_smi_range pval in
  let smi = Uint64.to_tagged_signed pval in
  let heap_number = pval |> Uint64.to_float64 in
  let value = Bool.ite is_in_smi_range smi heap_number in
  state |> State.update ~value

(* Deoptimization condition =
 *  LostPrecision(pval)
 *  \/ (hint=CheckForMinusZero /\ pval = -0.0)
 *)
let checked_float64_to_int32 hint pval state =
  let value32 = pval |> Float64.to_int32 in
  let deopt =
    let lost_precision =
      Bool.not (Float64.eq pval (value32 |> Int32.to_float64))
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
  let value = pval |> Int64.to_int Type.int32 32 in
  let deopt =
    (* lost-precision *)
    Bool.not (Value.eq pval (value |> Int32.to_int Type.int64 64))
  in
  state |> State.update ~value ~control ~deopt

(* Deoptimization condition =
 *  IsNotTaggedSigned(pval)
 * Assertion =
 *  value = ite well-defined Int32(pval >> 1) UV *)
let checked_tagged_signed_to_int32 pval state =
  let deopt = Bool.not (Value.has_type Type.tagged_signed pval) in
  let value = TaggedSigned.to_int32 pval in
  state |> State.update ~value ~deopt

let checked_tagged_to_float64 hint pval mem state =
  let is_tagged_signed = pval |> Value.has_type Type.tagged_signed in
  let is_tagged_pointer = pval |> Value.has_type Type.tagged_pointer in
  let map_check =
    check_map_for_heap_number_or_oddball_to_float64 hint pval mem
  in
  let deopt =
    Bool.ors
      [
        Bool.not (pval |> Value.has_type Type.any_tagged);
        Bool.ands [ is_tagged_pointer; Bool.not map_check ];
      ]
  in
  let value =
    Bool.ite is_tagged_signed
      (TaggedSigned.to_float64 pval)
      (HeapNumber.load pval mem |> HeapNumber.to_float64)
  in
  state |> State.update ~value ~deopt

let checked_tagged_to_tagged_pointer pval _checkpoint control state =
  let deopt = pval |> Value.has_type Type.tagged_signed in
  state |> State.update ~value:pval ~control ~deopt

let checked_tagged_to_tagged_signed pval _checkpoint control state =
  let deopt = Bool.not (pval |> Value.has_type Type.tagged_signed) in
  state |> State.update ~value:pval ~control ~deopt

let checked_truncate_tagged_to_word32 hint pval mem state =
  let deopt =
    let map_check =
      check_map_for_heap_number_or_oddball_to_float64 hint pval mem
    in
    Bool.ors
      [
        Bool.not (pval |> Value.has_type Type.any_tagged);
        Bool.ands
          [ pval |> Value.has_type Type.tagged_pointer; Bool.not map_check ];
      ]
  in
  let value =
    Bool.ite
      (pval |> Value.has_type Type.tagged_signed)
      (TaggedSigned.to_int32 pval)
      (HeapNumber.load pval mem |> HeapNumber.to_float64 |> Float64.to_int32)
  in
  state |> State.update ~value ~deopt

let checked_uint32_to_int32 pval state =
  let deopt = Int32.is_negative pval in
  let value = pval |> Uint32.to_int Type.int32 32 in
  state |> State.update ~value ~deopt

let number_to_boolean pval mem state =
  let value = pval |> Number.to_boolean mem in
  state |> State.update ~value

let number_to_int32 pval mem state =
  let value = pval |> Number.to_int32 mem in
  state |> State.update ~value

(* pure: 1V -> 1V *)
let number_to_uint32 pval mem state =
  let value = pval |> Number.to_uint32 mem in
  state |> State.update ~value

let speculative_to_number pval () control mem (state : State.t) =
  let rf = state.register_file in
  let deopt =
    Bool.not
      (Bool.ors
         [
           Number.is_number pval mem;
           pval |> Value.has_type Type.bool;
           pval |> Objects.is_null mem;
           pval |> Objects.is_undefined mem;
           pval |> Objects.is_boolean mem;
           pval |> Constant.is_empty_string rf;
         ])
  in
  let value =
    Bool.ite
      (Number.is_number pval mem)
      (pval |> Number.to_float64 mem)
      (Bool.ite
         (pval |> Objects.is_undefined mem)
         Float64.nan
         (Bool.ite
            (pval |> Objects.is_null mem)
            Float64.zero
            (Bool.ite
               (Bool.ors
                  [ pval |> Value.is_true; pval |> Constant.is_true_cst rf ])
               (Float64.from_numeral 1.0) (Float64.from_numeral 0.0))))
  in
  state |> State.update ~value ~deopt ~control

let to_boolean pval mem (state : State.t) =
  let rf = state.register_file in
  let _uif =
    let value_sort = BV.mk_sort ctx Value.len in
    Z3.FuncDecl.mk_func_decl_s ctx "to_boolean" [ value_sort ] Bool.mk_sort
  in
  (* https://tc39.es/ecma262/#sec-toboolean *)
  let value =
    Bool.ite
      (Number.is_number pval mem)
      (* number *)
      (pval |> Number.to_boolean mem)
      (Bool.ite
         (* undefined *)
         (pval |> Constant.is_undefined rf)
         Value.fl
         (Bool.ite
            (* boolean *)
            (pval |> Value.has_type Type.bool)
            pval
            (Bool.ite
               (pval |> Constant.is_true_cst rf)
               Value.tr
               (Bool.ite
                  (pval |> Constant.is_false_cst rf)
                  Value.fl
                  (Bool.ite
                     (* empty string *)
                     (pval |> Constant.is_empty_string rf)
                     Value.fl
                     (* null *)
                     (Bool.ite
                        (pval |> Constant.is_null rf)
                        Value.fl
                        (* otherwise, return true: can be improved *)
                        Value.tr))))))
  in
  state |> State.update ~value

let truncate_tagged_to_bit pval mem (state : State.t) =
  let rf = state.register_file in
  let _uif =
    let value_sort = BV.mk_sort ctx Value.len in
    Z3.FuncDecl.mk_func_decl_s ctx "to_boolean" [ value_sort ] Bool.mk_sort
  in
  let value =
    let number = HeapNumber.load pval mem in
    Bool.ite
      (* if [pval] is smi, return [pval] != 0 *)
      (pval |> Value.has_type Type.tagged_signed)
      (Bool.ite (TaggedSigned.is_zero pval) Value.fl Value.tr)
      (Bool.ite
         (* if [pval] is heap number, return [pval] != 0.0, -0.0 or NaN *)
         (pval |> Objects.is_heap_number mem)
         (Bool.ite
            (Bool.ors
               [
                 HeapNumber.is_minus_zero number;
                 HeapNumber.is_zero number;
                 HeapNumber.is_nan number;
               ])
            Value.fl Value.tr)
         (Bool.ite
            (* if [pval] is undefined, return false *)
            (pval |> Constant.is_undefined rf)
            Value.fl
            (Bool.ite
               (* if [pval] is true, return true *)
               (pval |> Constant.is_true_cst rf)
               Value.tr
               (Bool.ite
                  (* if [pval] is false, return false *)
                  (pval |> Constant.is_false_cst rf)
                  Value.fl
                  (* if [pval] is empty string, return false *)
                  (Bool.ite
                     (pval |> Constant.is_empty_string rf)
                     Value.fl
                     (* if [pval] is null, return false *)
                     (Bool.ite
                        (pval |> Constant.is_null rf)
                        Value.fl (* otherwise return true: can be improved *)
                        Value.tr))))))
  in
  state |> State.update ~value

(* check *)
let check_if cond _eff control state =
  let deopt = Bool.ite (Value.is_false cond) Bool.tr Bool.fl in
  state |> State.update ~deopt ~control

(* bound-check *)
let checked_uint32_bounds flag lval rval _eff control state =
  let check = Uint32.lt lval rval in
  if flag = "0" then
    state |> State.update ~value:lval ~deopt:(Bool.not check) ~control
  else if flag = "2" then
    (* AbortOnOutOfBounds *)
    state |> State.update ~value:lval ~ub:(Bool.not check) ~control
  else failwith "not implemented"
