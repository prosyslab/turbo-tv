open Z3utils
open ValueOperator
module Objects = Memory.Objects
module Repr = MachineType.Repr

(* helper functions *)
let object_is_smi_ pval = Word32.eqi (Word32.andi pval 1) 0

let check_map_for_heap_number_or_oddball_to_float64 hint pval mem =
  let is_heap_number = pval |> Value.has_type Type.float64 in
  let is_boolean = pval |> Objects.is_boolean mem in
  let is_oddball = pval |> Objects.is_oddball mem in
  match hint with
  | "Number" -> is_heap_number
  | "NumberOrBoolean" -> Bool.ors [ is_heap_number; is_boolean ]
  | "NumberOrOddball" -> Bool.ors [ is_heap_number; is_oddball ]
  | _ ->
      failwith (Printf.sprintf "CheckedTaggedToFloat64: Undefined hint %s" hint)

let type_guard hint values rf mem =
  if hint = "NumberOrBoolean" || hint = "NumberOrOddball" then
    Bool.ands
      (values
      |> List.map (fun v ->
             Bool.ors
               [
                 Number.is_number v mem;
                 v |> Value.has_type Type.bool;
                 v |> Constant.is_boolean_cst rf;
               ]))
  else Number.are_numbers values mem

let number_unary op pval mem state =
  let rf = state.State.register_file in
  let num = pval |> Number.to_number rf mem in
  let value = op num mem in
  state |> State.update ~value

let number_binary op lval rval mem state =
  let rf = state.State.register_file in
  let lnum = lval |> Number.to_number rf mem in
  let rnum = rval |> Number.to_number rf mem in
  let value = op lnum rnum mem in
  state |> State.update ~value

let speculative_number_unary hint op pval _eff control mem state =
  let deopt =
    Bool.not (type_guard hint [ pval ] state.State.register_file mem)
  in
  number_unary op pval state.State.memory state |> State.update ~deopt ~control

let speculative_number_binary hint op lval rval _eff control mem state =
  let deopt =
    Bool.not (type_guard hint [ lval; rval ] state.State.register_file mem)
  in
  number_binary op lval rval mem state |> State.update ~deopt ~control

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

let checked_int64_add lval rval _eff control state =
  let deopt = Int64.add_would_overflow lval rval in
  state |> Machine.int64_add lval rval |> State.update ~deopt ~control

let checked_int64_div lval rval _eff control state =
  let deopt =
    let division_by_zero = Int64.is_zero rval in
    let overflow =
      Bool.ands
        [ Int64.eq Int64.min_limit lval; Int64.eq rval (Value.from_int (-1)) ]
    in
    Bool.ors [ division_by_zero; overflow ]
  in
  state |> Machine.int64_div lval rval control |> State.update ~deopt ~control

let checked_int64_mod lval rval _eff control state =
  let deopt =
    let division_by_zero = Int64.is_zero rval in
    let overflow =
      Bool.ands
        [ Int64.eq Int64.min_limit lval; Int64.eq rval (Value.from_int (-1)) ]
    in
    Bool.ors [ division_by_zero; overflow ]
  in
  state |> Machine.int64_mod lval rval control |> State.update ~deopt ~control

let checked_int64_mul lval rval _eff control state =
  let deopt = Int64.mul_would_overflow lval rval in
  state |> Machine.int64_mul lval rval |> State.update ~deopt ~control

let checked_int64_sub lval rval _eff control state =
  let deopt = Int64.sub_would_overflow lval rval in
  state |> Machine.int64_sub lval rval |> State.update ~deopt ~control

let checked_uint32_div lval rval _eff control state =
  let deopt =
    let division_by_zero = Uint32.is_zero rval in
    let lost_precision =
      Bool.not (Uint32.eq (Uint32.urem lval rval) Uint32.zero)
    in
    Bool.ors [ division_by_zero; lost_precision ]
  in
  state |> Machine.uint32_div lval rval control |> State.update ~deopt ~control

let number_abs = number_unary Number.abs

let number_add = number_binary Number.add

let number_ceil = number_unary Number.ceil

let number_divide = number_binary Number.divide

let number_expm1 = number_unary Number.expm1

let number_floor = number_unary Number.floor

let number_imul lval rval mem state =
  let rf = state.State.register_file in
  let value =
    let res = Number.imul lval rval rf mem in
    Bool.ite
      (res |> Int32.is_in_smi_range)
      (res |> Int32.to_tagged_signed)
      (res |> Int32.to_float64)
  in
  state |> State.update ~value

let number_max = number_binary Number.max

let number_min = number_binary Number.min

let number_modulus = number_binary Number.remainder

let number_multiply = number_binary Number.multiply

let number_round = number_unary Number.round

let number_sign = number_unary Number.sign

let number_sin = number_unary Number.sin

let number_trunc = number_unary Number.trunc

let number_subtract = number_binary Number.subtract

let speculative_number_add hint = speculative_number_binary hint Number.add

let speculative_number_divide hint =
  speculative_number_binary hint Number.divide

let speculative_number_modulus hint =
  speculative_number_binary hint Number.remainder

let speculative_number_multiply hint =
  speculative_number_binary hint Number.multiply

let speculative_number_subtract hint =
  speculative_number_binary hint Number.subtract

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
  let rf = state.State.register_file in
  let true_cst = RegisterFile.find "true" rf in
  let false_cst = RegisterFile.find "false" rf in
  let value =
    Bool.ite
      (Bool.ors [ pval |> Value.is_false; pval |> Constant.is_false_cst rf ])
      true_cst false_cst
  in
  state |> State.update ~value

(* 2V -> 1V *)
let number_shift_left lval rval mem state =
  let rf = state.State.register_file in
  let value = Number.left_shift lval rval rf mem in
  state |> State.update ~value

let number_shift_right lval rval mem state =
  let rf = state.State.register_file in
  let value = Number.signed_right_shfit lval rval rf mem in
  state |> State.update ~value

let number_shift_right_logical lval rval mem state =
  let rf = state.State.register_file in
  let value = Number.unsigned_right_shift lval rval rf mem in
  state |> State.update ~value

let number_bitwise op lval rval mem state =
  let value = Number.bitwise op lval rval mem in
  state |> State.update ~value

let speculative_number_bitwise op hint lval rval _eff control mem state =
  let deopt =
    Bool.not (type_guard hint [ lval; rval ] state.State.register_file mem)
  in
  state |> number_bitwise op lval rval mem |> State.update ~deopt ~control

let speculative_number_shift_left hint lval rval _eff control mem state =
  let deopt =
    Bool.not (type_guard hint [ lval; rval ] state.State.register_file mem)
  in
  state |> number_shift_left lval rval mem |> State.update ~control ~deopt

let speculative_number_shift_right hint lval rval _eff control mem state =
  let deopt =
    Bool.not (type_guard hint [ lval; rval ] state.State.register_file mem)
  in
  state |> number_shift_right lval rval mem |> State.update ~control ~deopt

let speculative_number_shift_right_logical hint lval rval _eff control mem state
    =
  let deopt =
    Bool.not (type_guard hint [ lval; rval ] state.State.register_file mem)
  in
  state
  |> number_shift_right_logical lval rval mem
  |> State.update ~control ~deopt

(* simplified: comparison *)
let number_equal lnum rnum mem state =
  let rf = state.State.register_file in
  let true_cst = RegisterFile.find "true" rf in
  let false_cst = RegisterFile.find "false" rf in
  let value =
    Bool.ite (Value.is_false (Number.equal lnum rnum mem)) false_cst true_cst
  in
  state |> State.update ~value

let number_less_than lnum rnum mem state =
  let rf = state.State.register_file in
  let true_cst = RegisterFile.find "true" rf in
  let false_cst = RegisterFile.find "false" rf in
  (* https://tc39.es/ecma262/#sec-relational-operators-runtime-semantics-evaluation *)
  let value =
    let r = Number.less_than lnum rnum mem in
    Bool.ite
      (Bool.ors [ r |> Value.is_undefined; r |> Value.is_false ])
      false_cst true_cst
  in
  state |> State.update ~value

let number_less_than_or_equal lnum rnum mem state =
  let rf = state.State.register_file in
  let true_cst = RegisterFile.find "true" rf in
  let false_cst = RegisterFile.find "false" rf in
  (* https://tc39.es/ecma262/#sec-relational-operators-runtime-semantics-evaluation *)
  let value =
    let r = Number.less_than rnum lnum mem in
    Bool.ite
      (Bool.ors [ r |> Value.is_true; r |> Value.is_undefined ])
      false_cst true_cst
  in
  state |> State.update ~value

let number_same_value lnum rnum mem state =
  let value = Bool.ite (Number.same_value lnum rnum mem) Value.tr Value.fl in
  state |> State.update ~value

let reference_equal lval rval mem state =
  let rf = state.State.register_file in
  let is_heap_number_or_f64 value =
    Bool.ors
      [
        value |> Value.has_type Type.float64;
        value |> Objects.is_heap_number mem;
      ]
  in
  let value =
    if Strings.is_string lval mem && Strings.is_string rval mem then
      let l_val = Strings.load lval mem in
      let r_val = Strings.load rval mem in
      Strings.equal l_val r_val
    else if Strings.is_string lval mem || Strings.is_string rval mem then
      Value.fl
    else
      Bool.ite
        (Bool.ands [ is_heap_number_or_f64 lval; is_heap_number_or_f64 rval ])
        (Number.equal lval rval mem)
        (Bool.ite
           (Bool.ors [ is_heap_number_or_f64 lval; is_heap_number_or_f64 rval ])
           Value.fl
           (Bool.ite
              (TaggedSigned.eq_with_heap_constant lval rval rf)
              Value.tr
              (Bool.ite (Word32.eq lval rval) Value.tr Value.fl)))
  in
  state |> State.update ~value

let same_value lval rval mem state =
  let rf = state.State.register_file in
  let true_cst = RegisterFile.find "true" rf in
  let false_cst = RegisterFile.find "false" rf in
  let value =
    Bool.ite
      (Number.are_numbers [ lval; rval ] mem)
      (Bool.ite (Number.same_value lval rval mem) true_cst false_cst)
      (Bool.ite (Value.eq lval rval) true_cst false_cst)
  in
  state |> State.update ~value

let speculative_number_equal hint lval rval _eff control mem state =
  let deopt =
    Bool.not (type_guard hint [ lval; rval ] state.State.register_file mem)
  in
  state |> number_equal lval rval mem |> State.update ~deopt ~control

let speculative_number_less_than hint lval rval _eff control mem state =
  let deopt =
    Bool.not (type_guard hint [ lval; rval ] state.State.register_file mem)
  in
  state |> number_less_than lval rval mem |> State.update ~deopt ~control

let speculative_number_less_than_or_equal hint lval rval _eff control mem state
    =
  let deopt =
    Bool.not (type_guard hint [ lval; rval ] state.State.register_file mem)
  in
  state
  |> number_less_than_or_equal lval rval mem
  |> State.update ~deopt ~control

(* simplified: memory *)
let allocate_raw size control mem state =
  let ptr, mem = Memory.allocate size mem in
  state |> State.update ~value:ptr ~control ~mem

let load_element header_size repr bid ind control mem state =
  let off =
    BitVec.addi
      (BitVec.shli ind (MachineType.Repr.element_size_log2_of repr))
      header_size
  in
  state |> Machine.load bid off repr control mem

let load_field offset repr ptr _eff control mem state =
  let off = offset |> BitVecVal.from_int ~len:Value.len in
  let moved = TaggedPointer.move ptr off in
  let ty = Type.from_repr repr |> List.hd in
  let raw_ptr = moved |> TaggedPointer.to_raw_pointer in
  let value =
    let v =
      Memory.Bytes.load_as raw_ptr repr mem
      |> BitVec.zero_extend (64 - Repr.width_of repr)
      |> Value.entype ty
    in
    (* if memory is angelic, loading the tagged value always succeeds *)
    if ty = Type.tagged_signed then
      Bool.ite
        (moved |> Memory.is_angelic mem)
        (BitVec.shli (BitVec.lshri v 1) 1)
        v
    else if ty = Type.tagged_pointer then
      Bool.ite (moved |> Memory.is_angelic mem) (BitVec.ori v 1) v
    else v
  in
  let ub = Bool.not (Memory.can_access_as moved repr mem) in
  let assertion =
    Bool.implies control
      (Bool.eq (ptr |> TaggedPointer.bid_of) (moved |> TaggedPointer.bid_of))
  in
  let access =
    State.AccessInfo.
      {
        bid = ptr |> TaggedPointer.bid_of;
        is_read = true;
        lower = off |> TaggedPointer.off_of;
        upper = BitVec.addi (off |> TaggedPointer.off_of) (repr |> Repr.size_of);
      }
  in
  let is_angelic_value = moved |> Memory.is_angelic mem in
  {
    state with
    access_info = State.AccessInfo.add state.State.pc access state.access_info;
  }
  |> State.update ~value ~control ~ub ~is_angelic_value ~assertion

let load_typed_element array_type base extern ind control mem state =
  let bid = BitVec.addb base extern in
  let _, header_size, machine_type =
    MachineType.for_type_array_element array_type true
  in
  let repr = MachineType.repr machine_type in
  state |> load_element header_size repr bid ind control mem

(* V2E1C1 -> E1 *)
let store_element header_size repr bid ind value mem control state =
  let off =
    BitVec.addi
      (BitVec.shli ind (MachineType.Repr.element_size_log2_of repr))
      header_size
  in
  let ty = Type.from_repr repr |> List.hd in
  let value =
    Bool.ite
      (value |> Value.has_type Type.float64)
      (if ty = Type.tagged_signed then Float64.to_tagged_signed value
      else if ty = Type.any_tagged || ty = Type.float64 then value
      else if ty = Type.int64 then Float64.to_int64 value
      else if ty = Type.float32 then value
      else if ty = Type.int32 then Float64.to_int32 value
      else if ty = Type.int16 then Float64.to_int16 value
      else if ty = Type.int8 then Float64.to_int8 value
      else
        Format.sprintf "not implemented: %s" (ty |> Expr.to_simplified_string)
        |> failwith)
      value
  in
  state |> Machine.store bid off repr value control mem |> State.update ~control

let store_field ptr offset repr value _eff control mem state =
  let off = offset |> BitVecVal.from_int ~len:Value.len in
  let moved = TaggedPointer.move ptr off in
  let ub = Bool.not (Memory.can_access_as moved repr mem) in
  let raw_ptr = moved |> TaggedPointer.to_raw_pointer in
  let mem = Memory.Bytes.store_as (Bool.not ub) raw_ptr repr value mem in
  let access =
    State.AccessInfo.
      {
        bid = ptr |> TaggedPointer.bid_of;
        is_read = true;
        lower = off |> TaggedPointer.off_of;
        upper = BitVec.addi (off |> TaggedPointer.off_of) (repr |> Repr.size_of);
      }
  in
  let assertion =
    Bool.implies control
      (Bool.implies
         (ptr |> Value.has_type Type.tagged_pointer)
         (Bool.eq (ptr |> TaggedPointer.bid_of) (moved |> TaggedPointer.bid_of)))
  in
  {
    state with
    access_info = State.AccessInfo.add state.State.pc access state.access_info;
  }
  |> State.update ~control ~mem ~ub ~assertion

(* simplified: type-check *)

let number_is_integer pval mem state =
  let value = Bool.ite (pval |> Number.is_integer mem) Value.tr Value.fl in
  state |> State.update ~value

let number_is_safe_integer pval mem state =
  let value = Bool.ite (pval |> Number.is_safe_integer mem) Value.tr Value.fl in
  state |> State.update ~value

let number_is_minus_zero pval mem state =
  let value = Bool.ite (pval |> Number.is_minus_zero mem) Value.tr Value.fl in
  state |> State.update ~value

let number_is_nan pval mem state =
  let value = Bool.ite (pval |> Number.is_nan mem) Value.tr Value.fl in
  state |> State.update ~value

(* simplified: bigint *)
let integral32_or_minus_zero_to_bigint pval mem state =
  let rf = state.State.register_file in
  let val_i32 = pval |> Number.to_int32 rf mem in
  let bn =
    let sign = val_i32 |> Int32.is_negative in
    let value = Bool.ite sign (Int32.neg val_i32) val_i32 in
    Bigint.create (Bool.ite sign Bigint.neg_sign Bigint.pos_sign) value
  in
  let value, mem = Bigint.allocate bn mem in
  state |> State.update ~value ~mem

let bigint_binary op lval rval mem state =
  let l_bn = Bigint.load lval mem in
  let r_bn = Bigint.load rval mem in
  let v_bn = op l_bn r_bn in
  let value, mem = Bigint.allocate v_bn mem in
  state |> State.update ~value ~mem

let bigint_add = bigint_binary Bigint.add

let bigint_subtract = bigint_binary Bigint.sub

let bigint_multiply = bigint_binary Bigint.mul

let bigint_divide = bigint_binary Bigint.div

let bigint_modulus = bigint_binary Bigint.rem

let bigint_negate pval mem state =
  let p_bn = Bigint.load pval mem in
  let v_bn = Bigint.neg p_bn in
  let value, mem = Bigint.allocate v_bn mem in
  state |> State.update ~value ~mem

let bigint_bitwise_and = bigint_binary Bigint.bitwise_and

let bigint_bitwise_or = bigint_binary Bigint.bitwise_or

let bigint_bitwise_xor = bigint_binary Bigint.bitwise_xor

let bigint_shift_left = bigint_binary Bigint.shift_left

let bigint_shift_right = bigint_binary Bigint.shift_right

let bigint_compare op lval rval mem state =
  let l_bn = Bigint.load lval mem in
  let r_bn = Bigint.load rval mem in
  let value = Bool.ite (op l_bn r_bn) Value.tr Value.fl in
  state |> State.update ~value ~mem

let bigint_equal = bigint_compare Bigint.equal

let bigint_less_than = bigint_compare Bigint.less_than

let bigint_less_than_or_equal = bigint_compare Bigint.less_than_or_equal

let check_big_int value control mem state =
  let deopt = Bool.not (Objects.is_big_int mem value) in
  state |> State.update ~value ~deopt ~control

let checked_bigint_to_bigint64 value control mem state =
  let loaded = Bigint.load value mem in
  let is_int64_min =
    Bool.ands
      [ Bigint.is_negative loaded; BitVec.eqb loaded.value Int64.min_limit ]
  in
  let is_in_range = BitVec.uleb loaded.value Int64.max_limit in
  let deopt = Bool.ands [ Bool.not is_in_range; Bool.not is_int64_min ] in
  state |> State.update ~value ~control ~deopt

let truncate_big_int_to_word64 value mem state =
  let loaded = Bigint.load value mem in
  let value = Bigint.to_int64 loaded in
  state |> State.update ~value

(* bigint converter *)
let speculative_bigint_as ty nbits pval mem state =
  let deopt = Bool.not (pval |> Objects.is_big_int mem) in
  let nbits = nbits |> int_of_string in
  if nbits < 0 || nbits > 64 then
    (* 0 <= {nbits} <= 64 is assumed by TurboFan*)
    state |> State.update ~ub:(Bool.not deopt)
  else
    let bn = Bigint.load pval mem in
    let transformed =
      match ty with
      | "int" -> bn |> Bigint.as_intN nbits
      | "uint" -> bn |> Bigint.as_uintN nbits
      | _ -> failwith "unreachable"
    in
    let value, mem = Bigint.allocate transformed mem in
    state |> State.update ~value ~deopt ~mem

let speculative_bigint_binary op lval rval mem state =
  let deopt =
    Bool.not
      (Bool.ands
         [ lval |> Objects.is_big_int mem; rval |> Objects.is_big_int mem ])
  in
  state |> op lval rval mem |> State.update ~deopt

(* bigint arithmetic *)
let speculative_bigint_add = speculative_bigint_binary bigint_add

let speculative_bigint_subtract = speculative_bigint_binary bigint_subtract

let speculative_bigint_multiply = speculative_bigint_binary bigint_multiply

let speculative_bigint_divide = speculative_bigint_binary bigint_divide

let speculative_bigint_modulus = speculative_bigint_binary bigint_modulus

let speculative_bigint_negate pval mem state =
  let deopt = Bool.not (pval |> Objects.is_big_int mem) in
  state |> bigint_negate pval mem |> State.update ~deopt

let speculative_bigint_shift_left = speculative_bigint_binary bigint_shift_left

let speculative_bigint_shift_right =
  speculative_bigint_binary bigint_shift_right

(* bigint bitwise *)
let speculative_bigint_bitwise_and =
  speculative_bigint_binary bigint_bitwise_and

let speculative_bigint_bitwise_or = speculative_bigint_binary bigint_bitwise_or

let speculative_bigint_bitwise_xor =
  speculative_bigint_binary bigint_bitwise_xor

let speculative_bigint_compare op lval rval mem state =
  let deopt =
    Bool.not
      (Bool.ands
         [ lval |> Objects.is_big_int mem; rval |> Objects.is_big_int mem ])
  in
  state |> op lval rval mem |> State.update ~deopt

(* bigint comparison *)
let speculative_bigint_equal = speculative_bigint_compare bigint_equal

let speculative_bigint_less_than = speculative_bigint_compare bigint_less_than

let speculative_bigint_less_than_or_equal =
  speculative_bigint_compare bigint_less_than_or_equal

(* simplified: object *)

let object_is_minus_zero pval mem state =
  let rf = state.State.register_file in
  let true_cst = RegisterFile.find "true" rf in
  let false_cst = RegisterFile.find "false" rf in
  let value =
    Bool.ite
      (Bool.ors
         [
           pval |> Objects.is_heap_number mem;
           pval |> Value.has_type Type.float64;
         ])
      (Bool.ite (pval |> Number.is_minus_zero mem) true_cst false_cst)
      false_cst
  in
  state |> State.update ~value

let object_is_nan pval mem state =
  let rf = state.State.register_file in
  let true_cst = RegisterFile.find "true" rf in
  let false_cst = RegisterFile.find "false" rf in
  let value =
    Bool.ite
      (Bool.ors
         [
           pval |> Objects.is_heap_number mem;
           pval |> Value.has_type Type.float64;
         ])
      (Bool.ite (pval |> Number.is_nan mem) true_cst false_cst)
      false_cst
  in
  state |> State.update ~value

let object_is_smi pval state =
  let value = Bool.ite (Word32.eqi (Word32.andi pval 1) 0) Value.tr Value.fl in
  state |> State.update ~value

(* simplified: string *)
let check_string value control mem state =
  let deopt = Bool.not (Objects.is_string mem value) in
  state |> State.update ~value ~control ~deopt

let string_binary op lval rval mem state =
  let l_bn = Strings.load lval mem in
  let r_bn = Strings.load rval mem in
  let v_bn = op l_bn r_bn in
  let value, mem = Strings.allocate v_bn mem in
  state |> State.update ~value ~mem

let string_length pval mem state =
  let value = Strings.load pval mem |> Strings.length in
  state |> State.update ~value

let string_char_code_at s i mem state =
  let rf = state.State.register_file in
  let value =
    Strings.at (Strings.load s mem) (i |> Number.to_uint32 rf mem)
    |> Strings.str2num |> Value.cast Type.uint32
  in
  state |> State.update ~value

let string_code_point_at s i mem state =
  let rf = state.State.register_file in
  let value =
    Strings.at (Strings.load s mem) (i |> Number.to_uint32 rf mem)
    |> Strings.str2num |> Value.cast Type.uint32
  in
  state |> State.update ~value

let string_from_single_char_code c mem state =
  let c = c |> BitVec.extract 7 0 in
  let value, mem = Strings.allocate (Strings.from_char_bv c) mem in
  state |> State.update ~value ~mem

let string_from_single_code_point c mem state =
  let c = c |> BitVec.extract 15 0 in
  let value, mem = Strings.allocate (Strings.from_char_bv c) mem in
  state |> State.update ~value ~mem

let string_index_of l r i mem state =
  let rf = state.State.register_file in
  let l_val = Strings.load l mem in
  let r_val = Strings.load r mem in
  let value = Strings.index_of l_val r_val (i |> Number.to_uint32 rf mem) in
  state |> State.update ~value

let string_concat _ hd tl mem state =
  let hd_s = Strings.load hd mem in
  let tl_s = Strings.load tl mem in
  let v_s = Strings.concat hd_s tl_s in
  let value, mem = Strings.allocate v_s mem in
  state |> State.update ~value ~mem

let string_equal l r mem state =
  let rf = state.State.register_file in
  let l_val = Strings.load l mem in
  let r_val = Strings.load r mem in
  let true_cst = RegisterFile.find "true" rf in
  let false_cst = RegisterFile.find "false" rf in
  let value = Bool.ite (Bool.eq l_val.value r_val.value) true_cst false_cst in
  state |> State.update ~value

let string_less_than l r mem state =
  let l_val = Strings.load l mem in
  let r_val = Strings.load r mem in
  let value = Strings.lt l_val r_val in
  state |> State.update ~value

let string_less_than_or_equal l r mem state =
  let l_val = Strings.load l mem in
  let r_val = Strings.load r mem in
  let value = Strings.le l_val r_val in
  state |> State.update ~value

let string_sub_string s l_i r_i mem state =
  let rf = state.State.register_file in
  let s_val = Strings.load s mem in
  let v_s =
    Strings.sub_string s_val
      (l_i |> Number.to_uint32 rf mem)
      (r_i |> Number.to_uint32 rf mem)
  in
  let value, mem = Strings.allocate v_s mem in
  state |> State.update ~value ~mem

let string_to_number s mem state =
  let s_val = Strings.load s mem in
  let value = Strings.str2num s_val in
  state |> State.update ~value

(* simplified: type-conversion *)
let change_bit_to_tagged pval state =
  let rf = State.register_file state in
  let true_cst = RegisterFile.find "true" rf in
  let false_cst = RegisterFile.find "false" rf in
  let value =
    Bool.ite
      (pval |> Value.has_type Type.bool)
      (Bool.ite (pval |> Value.is_true) true_cst false_cst)
      (* if [pval] is not coming from cmp operator (e.g, Word32Cmp), just compare
         LSB 32-bit with 0*)
      (Bool.ite
         (pval |> Constant.is_true_cst rf)
         true_cst
         (Bool.ite
            (pval |> Constant.is_false_cst rf)
            false_cst
            (Bool.ite (pval |> Word32.eq Value.fl) false_cst true_cst)))
  in

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

let change_int64_to_bigint value mem state =
  let data = Value.data_of value in
  let sign = BitVec.lshri data 63 |> BitVec.extract 7 0 in
  let sign_mask = BitVec.ashri data 63 in
  let abs_value = BitVec.subb (BitVec.xor data sign_mask) sign_mask in
  let ptr, mem = Bigint.allocate (Bigint.create sign abs_value) mem in
  state |> State.update ~value:ptr ~mem

(* assertion:
 *  value = ite well-defined (tagged(pval)) UB *)
let change_int64_to_tagged pval state =
  (* if pval is in smi range, value = TaggedSigned(pval+pval) *)
  let is_in_smi_range = Int64.is_in_smi_range pval in
  let smi = pval |> Int64.to_tagged_signed in
  let heap_number = pval |> Int64.to_float64 in
  let value = Bool.ite is_in_smi_range smi heap_number in
  state |> State.update ~value

let change_tagged_to_bit pval state =
  let value =
    Bool.ite
      (pval |> Constant.is_true_cst state.State.register_file)
      Value.tr Value.fl
  in
  state |> State.update ~value

let change_tagged_to_float64 pval state =
  let value =
    Bool.ite
      (Value.has_type Type.int64 pval)
      (Int64.to_float64 pval)
      (Bool.ite
         (Value.has_type Type.tagged_signed pval)
         (TaggedSigned.to_float64 pval)
         pval)
  in
  state |> State.update ~value

let change_tagged_signed_to_int32 pval state =
  let value = TaggedSigned.to_int32 pval in
  state |> State.update ~value

let change_tagged_signed_to_int64 pval state =
  let value = TaggedSigned.to_int64 pval in
  state |> State.update ~value

let change_tagged_to_uint32 pval state =
  let value =
    Bool.ite (Value.has_type Type.float64 pval) (Float64.to_uint32 pval) pval
  in
  state |> State.update ~value

let change_uint32_to_tagged pval state =
  let is_in_smi_range = Uint32.is_in_smi_range pval in
  let smi = Uint32.to_tagged_signed pval in
  let heap_number = Uint32.to_float64 pval in
  let value = Bool.ite is_in_smi_range smi heap_number in
  state |> State.update ~value

let change_uint64_to_bigint pval mem state =
  let data = Value.data_of pval in
  let value, mem = Bigint.allocate (Bigint.create Bigint.pos_sign data) mem in
  state |> State.update ~value ~mem

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
        Bool.not
          (Bool.ors
             [
               pval |> Value.has_type Type.any_tagged;
               pval |> Value.has_type Type.float64;
             ]);
        Bool.ands [ is_tagged_pointer; Bool.not map_check ];
      ]
  in
  let value =
    Bool.ite is_tagged_signed
      (TaggedSigned.to_float64 pval)
      (Heapnumber.load pval mem |> Heapnumber.to_float64)
  in
  state |> State.update ~value ~deopt

let checked_tagged_to_int64 _hint pval mem state =
  let is_tagged_signed = pval |> Value.has_type Type.tagged_signed in
  let is_heap_number = pval |> Objects.is_heap_number mem in

  let deopt = Bool.not (Bool.ors [ is_tagged_signed; is_heap_number ]) in
  let value =
    Bool.ite is_tagged_signed
      (TaggedSigned.to_int64 pval)
      (Heapnumber.load pval mem |> Heapnumber.to_int64)
  in
  state |> State.update ~value ~deopt

let checked_tagged_to_tagged_pointer pval _checkpoint control state =
  let deopt = pval |> Value.has_type Type.tagged_signed in
  state |> State.update ~value:pval ~control ~deopt

let checked_tagged_to_tagged_signed pval _checkpoint control state =
  let deopt = Bool.not (pval |> object_is_smi_) in
  state |> State.update ~value:pval ~control ~deopt

let truncate_tagged_to_word32 pval state =
  let rf = state.State.register_file in
  let value =
    Bool.ite
      (pval |> Value.has_type Type.tagged_signed)
      (* number *)
      (TaggedSigned.to_int32 pval)
      (Bool.ite
         (pval |> Value.has_type Type.float64)
         (* number *)
         (Float64.to_int32 pval)
         (Bool.ite
            (Bool.ors
               (* false, null *)
               [ pval |> Constant.is_false_cst rf; pval |> Constant.is_null rf ])
            (Value.fl |> Value.cast Type.int32)
            (Bool.ite
               (pval |> Constant.is_true_cst rf)
               (* true *)
               (Value.tr |> Value.cast Type.int32)
               (* undefined *)
               (Float64.nan |> Float64.to_int32))))
  in

  state |> State.update ~value

let checked_truncate_tagged_to_word32 hint pval mem state =
  let deopt =
    let map_check =
      check_map_for_heap_number_or_oddball_to_float64 hint pval mem
    in
    Bool.ors
      [
        Bool.not
          (Bool.ors
             [
               pval |> Value.has_type Type.any_tagged;
               pval |> Value.has_type Type.float64;
             ]);
        Bool.ands
          [ pval |> Value.has_type Type.tagged_pointer; Bool.not map_check ];
      ]
  in
  state |> truncate_tagged_to_word32 pval |> State.update ~deopt

let checked_uint32_to_int32 pval state =
  let deopt = Int32.is_negative pval in
  let value = pval |> Uint32.to_int Type.int32 32 in
  state |> State.update ~value ~deopt

let number_to_boolean pval mem state =
  let value = pval |> Number.to_boolean mem in
  state |> State.update ~value

let number_to_int32 pval mem state =
  let rf = state.State.register_file in
  let value = pval |> Number.to_int32 rf mem in
  state |> State.update ~value

let number_to_string pval mem state =
  let rf = state.State.register_file in
  let v_s = pval |> Number.to_uint32 rf mem |> Strings.num2str in
  let value, mem = Strings.allocate v_s mem in
  state |> State.update ~value ~mem

(* pure: 1V -> 1V *)
let number_to_uint32 pval mem state =
  let rf = state.State.register_file in
  let value = pval |> Number.to_uint32 rf mem in
  state |> State.update ~value

let speculative_to_number hint pval () control mem state =
  let rf = state.State.register_file in
  let deopt =
    Bool.not (type_guard hint [ pval ] state.State.register_file mem)
  in
  let value = pval |> Number.to_number rf mem in
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
                  (* null *)
                  (Bool.ite
                     (pval |> Constant.is_null rf)
                     Value.fl
                     (* otherwise, return true: can be improved *)
                     Value.tr)))))
  in
  state |> State.update ~value

let truncate_tagged_to_bit pval mem (state : State.t) =
  let rf = state.register_file in
  (* ObjectIsSmi *)
  let is_smi pval =
    Bool.ands
      [
        Word32.eqi (Word32.andi pval 1) 0;
        Bool.not (pval |> Value.has_type Type.float64);
      ]
  in
  let value =
    Bool.ite (pval |> is_smi)
      (* if [pval] is smi, return [pval] != 0 *)
      (Bool.ite (TaggedSigned.is_zero pval) Value.fl Value.tr)
      (Bool.ite
         (* if [pval] is heap number, return [pval] != 0.0, -0.0 or NaN *)
         (Bool.ors
            [
              pval |> Objects.is_heap_number mem;
              pval |> Value.has_type Type.float64;
            ])
         (pval |> Number.to_boolean mem)
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
                  (* if [pval] is null, return false *)
                  (Bool.ite
                     (pval |> Constant.is_null rf)
                     Value.fl (* otherwise return true: can be improved *)
                     Value.tr)))))
  in

  state |> State.update ~value

let truncate_tagged_pointer_to_bit pval mem state =
  let rf = state.State.register_file in
  let value =
    Bool.ite
      (* if [pval] is heap number, return [pval] != 0.0, -0.0 or NaN *)
      (Bool.ors
         [
           pval |> Objects.is_heap_number mem;
           pval |> Value.has_type Type.float64;
         ])
      (pval |> Number.to_boolean mem)
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
               (* if [pval] is null, return false *)
               (Bool.ite
                  (pval |> Constant.is_null rf)
                  Value.fl (* otherwise return true: can be improved *)
                  Value.tr))))
  in
  state |> State.update ~value

(* check *)
let check_if cond _eff control state =
  let deopt = Bool.ite (Value.is_false cond) Bool.tr Bool.fl in
  state |> State.update ~deopt ~control

(* bound-check *)
let check_bounds flag lval rval _eff control mem state =
  let flag = flag |> int_of_string in
  let check = Uint64.lt lval rval in
  let deopt =
    Bool.ors
      [
        Bool.not
          (Bool.ors
             [
               lval |> Value.has_type Type.uint64;
               lval |> Value.has_type Type.uint32;
             ]);
        (if flag = 0 then
         Bool.ors [ Bool.not check; lval |> Number.is_minus_zero mem ]
        else if flag = 1 then Bool.tr
        else Bool.fl);
      ]
  in
  let ub = if flag = 2 || flag = 3 then Bool.not check else Bool.fl in
  state |> State.update ~value:lval ~deopt ~ub ~control

let checked_uint32_bounds flag lval rval _eff control state =
  let flag = flag |> int_of_string in
  let check = Uint32.lt lval rval in
  if flag = 0 then
    state |> State.update ~value:lval ~deopt:(Bool.not check) ~control
  else if flag = 2 then
    (* AbortOnOutOfBounds *)
    state |> State.update ~value:lval ~ub:(Bool.not check) ~control
  else failwith "not implemented"

let checked_uint64_bounds flag lval rval _eff control state =
  let flag = flag |> int_of_string in
  let check = Uint64.lt lval rval in
  if flag = 0 then
    state |> State.update ~value:lval ~deopt:(Bool.not check) ~control
  else if flag = 2 then
    (* AbortOnOutOfBounds *)
    state |> State.update ~value:lval ~ub:(Bool.not check) ~control
  else failwith "not implemented"

let checked_uint64_to_int64 pval state =
  let deopt = Int64.is_negative pval in
  let value = pval |> Uint64.to_int Type.int64 64 in
  state |> State.update ~value ~deopt

let ensure_writable_fast_elements _lval rval _eff control state =
  let value = rval in
  state |> State.update ~value ~control
