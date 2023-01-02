open Z3utils
open ValueOperator
module HeapNumber = Objects.HeapNumber
module Repr = MachineType.Repr

(* machine: arithmetic *)
let float64_abs pval state =
  let value = Float64.abs pval in
  state |> State.update ~value

let float64_add lval rval state =
  let value = Float64.add lval rval in
  state |> State.update ~value

let float64_asin value state =
  let value = Float64.asin value in
  state |> State.update ~value

let float64_asinh value state =
  let value = Float64.asinh value in
  state |> State.update ~value

let float64_div lval rval state =
  let value = Float64.div lval rval in
  state |> State.update ~value

let float64_neg pval state =
  let value = Float64.neg pval in
  state |> State.update ~value

(* to be fixed *)
let float64_extract_high_word32 pval state =
  let hword32 =
    pval |> Value.data_of |> BitVec.extract 63 32 |> BitVec.zero_extend 32
  in
  let value = Value.entype (Type.from_repr Repr.Word32 |> List.hd) hword32 in
  state |> State.update ~value

let float64_max lval rval state =
  let value = Float64.max lval rval in
  state |> State.update ~value

let float64_min lval rval state =
  let value = Float64.min lval rval in
  state |> State.update ~value

let float64_mod lval rval state =
  let value = Float64.modulo lval rval in
  state |> State.update ~value

let float64_mul lval rval state =
  let value = Float64.mul lval rval in
  state |> State.update ~value

let float64_pow lval rval state =
  let value = Float64.pow lval rval in
  state |> State.update ~value

let float64_sub lval rval state =
  let value = Float64.sub lval rval in
  state |> State.update ~value

let float64_round_down pval state =
  let value = pval |> Float64.round_down in
  state |> State.update ~value

let float64_round_up pval state =
  let value = pval |> Float64.round_up in
  state |> State.update ~value

let float64_round_ties_away pval state =
  let value = pval |> Float64.round_nearest_to_away in
  state |> State.update ~value

let float64_round_ties_even pval state =
  let value = pval |> Float64.round_nearest_to_even in
  state |> State.update ~value

let float64_round_truncate pval state =
  let value = pval |> Float64.trunc in
  state |> State.update ~value

let float64_sin pval state =
  let value = pval |> Float64.sin in
  state |> State.update ~value

let int_arith width op lval rval ?control state =
  let value =
    match (width, op) with
    | 32, "+" -> Int32.add lval rval
    | 32, "-" -> Int32.sub lval rval
    | 32, "*" -> Int32.mul lval rval
    | 32, "/" -> Int32.div lval rval
    | 32, "%" -> Int32.modulo lval rval
    | 64, "+" -> Int64.add lval rval
    | 64, "-" -> Int64.sub lval rval
    | 64, "*" -> Int64.mul lval rval
    | 64, "/" -> Int32.div lval rval
    | 64, "%" -> Int32.modulo lval rval
    | _ -> failwith "int_arith: not implemented"
  in
  match control with
  | None -> State.update ~value state
  | Some control -> State.update ~value ~control state

let int32_add lval rval state = int_arith 32 "+" lval rval state

let int32_sub lval rval state = int_arith 32 "-" lval rval state

let int32_mul lval rval state = int_arith 32 "*" lval rval state

let int32_div lval rval control state =
  int_arith 32 "/" lval rval ~control state

let int32_mod lval rval control state =
  int_arith 32 "%" lval rval ~control state

let int32_add_with_overflow lval rval control state =
  let added = Int32.add lval rval in
  let ovf = Bool.ite (Int32.add_would_overflow lval rval) Value.tr Value.fl in
  let value = Composed.from_values [ added; ovf ] in
  state |> State.update ~value ~control

let int32_mul_with_overflow lval rval control state =
  let multiplied = Int32.mul lval rval in
  let ovf = Bool.ite (Int32.mul_would_overflow lval rval) Value.tr Value.fl in
  let value = Composed.from_values [ multiplied; ovf ] in
  state |> State.update ~value ~control

let int32_sub_with_overflow lval rval control state =
  let subtracted = Int32.sub lval rval in
  let ovf = Bool.ite (Int32.sub_would_overflow lval rval) Value.tr Value.fl in
  let value = Composed.from_values [ subtracted; ovf ] in
  state |> State.update ~value ~control

let int64_add lval rval state = int_arith 64 "+" lval rval state

let int64_sub lval rval state = int_arith 64 "-" lval rval state

let int64_mul lval rval state = int_arith 64 "*" lval rval state

let int64_div lval rval control state =
  int_arith 64 "/" lval rval ~control state

let int64_mod lval rval control state =
  int_arith 64 "%" lval rval ~control state

let int64_add_with_overflow lval rval control state =
  let added = Int64.add lval rval in
  let ovf = Bool.ite (Int64.add_would_overflow lval rval) Value.tr Value.fl in
  let value = Composed.from_values [ added; ovf ] in
  state |> State.update ~value ~control

let int64_sub_with_overflow lval rval control state =
  let subtracted = Int64.sub lval rval in
  let ovf = Bool.ite (Int64.sub_would_overflow lval rval) Value.tr Value.fl in
  let value = Composed.from_values [ subtracted; ovf ] in
  state |> State.update ~value ~control

let int64_mul_with_overflow lval rval control state =
  let multiplied = Int64.mul lval rval in
  let ovf = Bool.ite (Int64.mul_would_overflow lval rval) Value.tr Value.fl in
  let value = Composed.from_values [ multiplied; ovf ] in
  state |> State.update ~value ~control

let round_float64_to_int32 pval state =
  let value = Float64.to_int32 pval in
  state |> State.update ~value

let uint32_div lval rval control state =
  let value = Uint32.div lval rval in
  state |> State.update ~value ~control

let uint32_mod lval rval control state =
  let value = Uint32.modulo lval rval in
  state |> State.update ~value ~control

let word_opsem width op lval rval state =
  let value =
    match (width, op) with
    | 32, "and" -> Word32.and_ lval rval
    | 32, "or" -> Word32.or_ lval rval
    | 32, "xor" -> Word32.xor lval rval
    | 32, "shl" -> Word32.shl lval rval
    | 32, "lshr" -> Word32.lshr lval rval
    | 32, "ashr" -> Word32.ashr lval rval
    | 32, "rol" -> Word32.rol lval rval
    | 32, "ror" -> Word32.ror lval rval
    | 64, "and" -> Word64.and_ lval rval
    | 64, "or" -> Word64.or_ lval rval
    | 64, "xor" -> Word64.xor lval rval
    | 64, "shl" -> Word64.shl lval rval
    | 64, "lshr" -> Word64.lshr lval rval
    | 64, "ashr" -> Word64.ashr lval rval
    | 64, "rol" -> Word64.rol lval rval
    | 64, "ror" -> Word64.ror lval rval
    | _ -> failwith "word_opsem: not implemented"
  in
  state |> State.update ~value

let word32_and lval rval state = word_opsem 32 "and" lval rval state

let word32_or lval rval state = word_opsem 32 "or" lval rval state

let word32_rol lval rval state = word_opsem 32 "rol" lval rval state

let word32_ror lval rval state = word_opsem 32 "ror" lval rval state

let word32_sar hint lval rval state =
  let cnt = Uint32.modulo rval (32 |> Value.from_int) in
  let shift_out = Word32.mask lval cnt in
  let hint_is_shift_out_zero = String.equal hint "ShiftOutZeros" in
  let wd_cond =
    if hint_is_shift_out_zero then Word32.eq shift_out Uint32.zero else Bool.tr
  in
  let ub = Bool.not wd_cond in
  state |> word_opsem 32 "ashr" lval rval |> State.update ~ub

let word32_shl lval rval state = word_opsem 32 "shl" lval rval state

let word32_shr lval rval state = word_opsem 32 "lshr" lval rval state

let word32_xor lval rval state = word_opsem 32 "xor" lval rval state

let word64_and lval rval state = word_opsem 64 "and" lval rval state

let word64_or lval rval state = word_opsem 64 "or" lval rval state

let word64_rol lval rval state = word_opsem 64 "rol" lval rval state

let word64_ror lval rval state = word_opsem 64 "ror" lval rval state

let word64_sar hint lval rval state =
  let cnt = Uint64.modulo rval (64 |> Value.from_int) in
  let shift_out = Word64.mask lval cnt in
  let hint_is_shift_out_zero = String.equal hint "ShiftOutZeros" in
  let wd_cond =
    if hint_is_shift_out_zero then Word64.eq shift_out Uint64.zero else Bool.tr
  in
  let ub = Bool.not wd_cond in
  state |> word_opsem 64 "ashr" lval rval |> State.update ~ub

let word64_shl lval rval state = word_opsem 64 "shl" lval rval state

let word64_shr lval rval state = word_opsem 64 "lshr" lval rval state

let word64_xor lval rval state = word_opsem 64 "xor" lval rval state

let word32_reverse_bytes v state =
  let value = v |> Word32.swap in
  state |> State.update ~value

let word64_reverse_bytes v state =
  let value = v |> Word64.swap in
  state |> State.update ~value

(* machine: comparison *)
let float64_equal lval rval state =
  let value = Bool.ite (Float64.eq lval rval) Value.tr Value.fl in
  state |> State.update ~value

let float64_less_than lval rval state =
  let value = Bool.ite (Float64.lt lval rval) Value.tr Value.fl in
  state |> State.update ~value

let float64_less_than_or_equal lval rval state =
  let value = Bool.ite (Float64.le lval rval) Value.tr Value.fl in
  state |> State.update ~value

let int_cmp sign width op lval rval state =
  let value =
    Bool.ite
      (match (sign, width, op) with
      | true, 32, "<" -> Int32.lt lval rval
      | true, 32, "<=" -> Int32.le lval rval
      | true, 32, "==" -> Int32.eq lval rval
      | true, 64, "<" -> Int64.lt lval rval
      | true, 64, "<=" -> Int64.le lval rval
      | true, 64, "==" -> Int64.eq lval rval
      | false, 32, "<" -> Uint32.lt lval rval
      | false, 32, "<=" -> Uint32.le lval rval
      | false, 32, "==" -> Uint32.eq lval rval
      | false, 64, "<" -> Uint64.lt lval rval
      | false, 64, "<=" -> Uint64.le lval rval
      | false, 64, "==" -> Uint64.eq lval rval
      | _ -> failwith "int_cmp: not implemented")
      Value.tr Value.fl
  in
  state |> State.update ~value

let int32_less_than = int_cmp true 32 "<"

let int32_less_than_or_equal = int_cmp true 32 "<="

let int32_equal = int_cmp true 32 "=="

let int64_less_than = int_cmp true 64 "<"

let int64_less_than_or_equal = int_cmp true 64 "<="

let int64_equal = int_cmp true 64 "=="

let uint32_less_than = int_cmp false 32 "<"

let uint32_less_than_or_equal = int_cmp false 32 "<="

let uint32_equal = int_cmp false 32 "=="

let uint64_less_than = int_cmp false 64 "<"

let uint64_less_than_or_equal = int_cmp false 64 "<="

let uint64_equal = int_cmp false 64 "=="

(* machine: conversion *)
let word32_equal lval rval state =
  let rf = state.State.register_file in
  let lval_is_zero = Value.eq lval Int32.zero in
  let rval_is_zero = Value.eq rval Int32.zero in
  let check_for_tf_constants =
    Bool.ors
      [
        Bool.ands [ Constant.is_false_cst rf lval; rval_is_zero ];
        Bool.ands [ lval_is_zero; Constant.is_false_cst rf rval ];
        Bool.ands [ Constant.is_true_cst rf lval; Bool.not rval_is_zero ];
        Bool.ands [ Bool.not lval_is_zero; Constant.is_true_cst rf rval ];
      ]
  in
  let value =
    Bool.ite
      (Bool.ors [ check_for_tf_constants; Word32.eq lval rval ])
      Value.tr Value.fl
  in
  state |> State.update ~value

let word64_equal lval rval state =
  let rf = state.State.register_file in
  let lval_is_zero = Value.eq lval Int64.zero in
  let rval_is_zero = Value.eq rval Int64.zero in
  let check_for_tf_constants =
    Bool.ors
      [
        Bool.ands [ Constant.is_false_cst rf lval; rval_is_zero ];
        Bool.ands [ lval_is_zero; Constant.is_false_cst rf rval ];
        Bool.ands [ Constant.is_true_cst rf lval; Bool.not rval_is_zero ];
        Bool.ands [ Bool.not lval_is_zero; Constant.is_true_cst rf rval ];
      ]
  in
  let value =
    Bool.ite
      (Bool.ors [ check_for_tf_constants; Word64.eq lval rval ])
      Value.tr Value.fl
  in
  state |> State.update ~value

(* machine: memory *)
(* well-defined condition:
 *   IsPointer(ptr) \/
 *   (IsTaggedPointer(ptr) /\ CanAccess(ptr, pos, repr))
 * assertion:
 *   mem = ite well-defined Store(ptr, pos, repr, mem) mem *)
let store ptr pos repr value mem state =
  let ub = Bool.not (Memory.can_access_as ptr repr mem) in
  let raw_ptr = TaggedPointer.move ptr pos |> TaggedPointer.to_raw_pointer in
  let mem = mem |> Memory.store_as (Bool.not ub) raw_ptr repr value in
  state |> State.update ~mem ~ub

(* well-defined condition:
 *   IsPointer(ptr) \/
 *   (IsTaggedPointer(ptr) /\ CanAccess(ptr, pos, repr))
 * assertion:
 *   value = (Mem[pos+size]) *)
let load ptr pos repr mem state =
  let ub = Bool.not (Memory.can_access_as ptr repr mem) in
  let raw_ptr = TaggedPointer.move ptr pos |> TaggedPointer.to_raw_pointer in
  let ty = Type.from_repr repr |> List.hd in
  let value =
    Memory.load_as raw_ptr repr mem
    |> BitVec.zero_extend (64 - Repr.width_of repr)
    |> Value.entype ty
  in
  state |> State.update ~value ~ub

(* machine: type-conversion *)
let bitcast_float32_to_int32 v state =
  let value = v |> Value.cast Type.int32 in
  state |> State.update ~value

let bitcast_float64_to_int64 v state =
  let value = v |> Value.cast Type.int64 in
  state |> State.update ~value

let bitcast_tagged_to_word v state =
  let ty = Type.from_repr Repr.Word64 |> List.hd in
  let value = v |> Value.cast ty in
  state |> State.update ~value

let bitcast_word32_to_word64 v state =
  let ty = Type.from_repr Repr.Word64 |> List.hd in
  let value = v |> Value.cast ty in
  state |> State.update ~value

let bitcast_word_to_tagged v state =
  let ty = Type.from_repr Repr.Tagged |> List.hd in
  let value = v |> Value.cast ty |> AnyTagged.settle in
  state |> State.update ~value

let change_float64_to_int32 pval state =
  let value = pval |> Float64.to_int32 in
  state |> State.update ~value

let change_float64_to_int64 pval state =
  let value = pval |> Float64.to_int64 in
  state |> State.update ~value

let change_float64_to_uint32 pval state =
  let value = pval |> Float64.to_uint32 in
  state |> State.update ~value

let change_float64_to_uint64 pval state =
  let value = pval |> Float64.to_uint64 in
  state |> State.update ~value

let change_int32_to_float64 pval state =
  let value = pval |> Int32.to_float64 in
  state |> State.update ~value

let change_int32_to_int64 pval state =
  let value = pval |> Int32.to_int Type.int64 64 in
  state |> State.update ~value

let change_int64_to_float64 pval state =
  let value = pval |> Int64.to_float64 in
  state |> State.update ~value

let change_uint32_to_float64 pval state =
  let value = pval |> Uint32.to_float64 in
  state |> State.update ~value

let change_uint32_to_uint64 pval state =
  let value = pval |> Uint32.to_int Type.uint64 64 in
  state |> State.update ~value

let truncate_float64_to_word32 pval state =
  let truncated = pval |> Float64.to_int32 in
  state |> State.update ~value:truncated

let truncate_int64_to_int32 pval state =
  let value = pval |> Int64.to_int Type.int32 32 in
  state |> State.update ~value
