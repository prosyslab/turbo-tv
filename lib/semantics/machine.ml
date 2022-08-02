open Z3utils
module HeapNumber = Objects.HeapNumber
module Composed = Value.Composed
module Repr = MachineType.Repr

(* machine: arithmetic *)
let float64_abs pval state =
  let value = Value.absf pval in
  state |> State.update ~value

let float64_add lval rval state =
  let value = Float64.add lval rval in
  state |> State.update ~value

let float64_div lval rval state =
  let value = Float64.div lval rval in
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
  let value = Float64.rem lval rval in
  state |> State.update ~value

let float64_mul lval rval state =
  let value = Float64.mul lval rval in
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

let float64_round_truncate pval state =
  let value = pval |> Float64.trunc in
  state |> State.update ~value

let float64_sin pval state =
  let value = pval |> Float64.sin in
  state |> State.update ~value

let int32_add lval rval state =
  let value = Value.Int32.add lval rval in
  state |> State.update ~value

(* assertion:
 * value = ((lval + rval) mod 2**32) :: (lval + rval > smi_max) *)
let int32_add_with_overflow lval rval control state =
  let added = Value.Int32.add lval rval in
  let ovf =
    Bool.ite (Value.Int32.add_would_overflow lval rval) Value.tr Value.fl
  in
  let value = Composed.from_values [ added; ovf ] in
  state |> State.update ~value ~control

let int32_div lval rval control state =
  let value = Value.Int32.div lval rval in
  state |> State.update ~value ~control

let int32_mul lval rval state =
  let value = Value.Int32.mul lval rval in
  state |> State.update ~value

let int32_mul_with_overflow lval rval control state =
  let multiplied = Value.Int32.mul lval rval in
  let ovf =
    Bool.ite (Value.Int32.mul_would_overflow lval rval) Value.tr Value.fl
  in
  let value = Composed.from_values [ multiplied; ovf ] in
  state |> State.update ~value ~control

let int32_sub lval rval state =
  let value = Value.Int32.sub lval rval in
  state |> State.update ~value

let int32_sub_with_overflow lval rval control state =
  let subtracted = Value.Int32.sub lval rval in
  let ovf =
    Bool.ite (Value.Int32.sub_would_overflow lval rval) Value.tr Value.fl
  in
  let value = Composed.from_values [ subtracted; ovf ] in
  state |> State.update ~value ~control

let int64_add lval rval state =
  let value = Value.Int64.add lval rval in
  state |> State.update ~value

let int64_sub lval rval state =
  let value = Value.sub lval rval in
  state |> State.update ~value

let round_float64_to_int32 pval state =
  let value = Float64.to_int32 pval in
  state |> State.update ~value

let uint32_div lval rval control state =
  let value = Value.Int32.div lval rval in
  state |> State.update ~value ~control

(* well-defined conditions:
 * (hint = "ShiftOutZero") ^ (cnt = (rval mod 32)) -> lval[-cnt:] = 0
 * assertion:
 * value = ite well-defined (lval >> (rval mod 32)) UB *)
let word32_sar hint lval rval state =
  let cnt = Value.modi rval 32 in
  let shift_out = Value.mask lval cnt in
  let hint_is_shift_out_zero = String.equal hint "ShiftOutZeros" in
  let wd_cond =
    if hint_is_shift_out_zero then Value.weak_eq shift_out Value.zero
    else Bool.tr
  in
  let value = Value.ashr lval cnt in
  let ub = Bool.not wd_cond in
  state |> State.update ~value ~ub

let word32_shl lval rval state =
  let value = Value.shl lval rval in
  state |> State.update ~value

let word32_shr lval rval state =
  let value = Value.lshr lval rval in
  state |> State.update ~value

let word32_xor lval rval state =
  let value = Value.xor lval rval in
  state |> State.update ~value

(* well-defined conditions:
 * (hint = "ShiftOutZero") ^ (cnt = (rval mod 64)) -> lval[-cnt:] = 0
 * assertion:
 * value = ite well-defined (lval >> (rval mod 64)) UB *)
let word64_sar hint lval rval state =
  let cnt = Value.modi rval 64 in
  let shift_out = Value.mask lval cnt in
  let hint_is_shift_out_zero = String.equal hint "ShiftOutZeros" in
  let wd_cond =
    if hint_is_shift_out_zero then Value.weak_eq shift_out Value.zero
    else Bool.tr
  in
  let value = Value.ashr lval cnt in
  let ub = Bool.not wd_cond in
  state |> State.update ~value ~ub

let word64_shl lval rval state =
  let value = Value.shl lval rval in
  state |> State.update ~value

let word32_reverse_bytes v state =
  let value = v |> Value.swap32 in
  state |> State.update ~value

let word64_reverse_bytes v state =
  let value = v |> Value.swap64 in
  state |> State.update ~value

(* machine: logic *)
let word32_and lval rval state =
  let value = Value.and_ Repr.Word32 lval rval in
  state |> State.update ~value

let word32_or lval rval state =
  let value = Value.or_ lval rval in
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

let int32_less_than lval rval state =
  let value = Bool.ite (Value.Int32.lt lval rval) Value.tr Value.fl in
  state |> State.update ~value

let int32_less_than_or_equal lval rval state =
  let value = Bool.ite (Value.Int32.le lval rval) Value.tr Value.fl in
  state |> State.update ~value

let int64_less_than lval rval state =
  let value = Bool.ite (Value.Int64.lt lval rval) Value.tr Value.fl in
  state |> State.update ~value

let word32_equal lval rval state =
  let value =
    Bool.ite (Value.weak_eq ~repr:Repr.Word32 lval rval) Value.tr Value.fl
  in
  state |> State.update ~value

let word64_equal lval rval state =
  let value =
    Bool.ite (Value.weak_eq ~repr:Repr.Word64 lval rval) Value.tr Value.fl
  in
  state |> State.update ~value

let uint32_less_than lval rval state =
  let value = Bool.ite (Value.ult lval rval) Value.tr Value.fl in
  state |> State.update ~value

let uint32_less_than_or_equal lval rval state =
  let value = Bool.ite (Value.ule lval rval) Value.tr Value.fl in
  state |> State.update ~value

let uint64_less_than lval rval state =
  let value = Bool.ite (Value.ult lval rval) Value.tr Value.fl in
  state |> State.update ~value

let uint64_less_than_or_equal lval rval state =
  let value = Bool.ite (Value.ule lval rval) Value.tr Value.fl in
  state |> State.update ~value

(* machine: memory *)
(* well-defined condition:
 *   IsPointer(ptr) \/
 *   (IsTaggedPointer(ptr) /\ CanAccess(ptr, pos, repr))
 * assertion:
 *   mem = ite well-defined Store(ptr, pos, repr, mem) mem *)
let store ptr pos repr value mem state =
  let deopt = Bool.not (ptr |> Value.has_type Type.pointer) in
  let ub =
    let ptr_is_tagged_pointer = Value.has_type Type.tagged_pointer ptr in
    let can_access = TaggedPointer.can_access_as pos repr ptr in
    (* only when value is tagged pointer, check boundary *)
    Bool.ands [ ptr_is_tagged_pointer; Bool.not can_access ]
  in
  let mem =
    mem
    |> Memory.store_as
         (TaggedPointer.move ptr pos |> TaggedPointer.to_raw_pointer)
         repr (Bool.not ub) value
  in
  state |> State.update ~mem ~ub ~deopt

(* well-defined condition:
 *   IsPointer(ptr) \/
 *   (IsTaggedPointer(ptr) /\ CanAccess(ptr, pos, repr))
 * assertion:
 *   value = (Mem[pos+size]) *)
let load ptr pos repr mem state =
  let deopt = Bool.not (ptr |> Value.has_type Type.pointer) in
  let ub =
    let ptr_is_tagged_pointer = Value.has_type Type.tagged_pointer ptr in
    let can_access = TaggedPointer.can_access_as pos repr ptr in
    (* only when value is tagged pointer, check boundary *)
    Bool.ands [ ptr_is_tagged_pointer; Bool.not can_access ]
  in
  (* Some repr can be mapped to more than one type.
     e.g. Repr.Word8-> [Type.int8; Type.uint8]
     In this case, we pick the head of the type candidates.*)
  let ty = Type.from_repr repr |> List.hd in
  let value =
    Memory.load_as
      (TaggedPointer.move ptr pos |> TaggedPointer.to_raw_pointer)
      repr mem
    |> Value.zero_extend_data |> Value.entype ty
  in
  state |> State.update ~value ~ub ~deopt

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
  let value = v |> Value.cast ty in
  state |> State.update ~value

let change_float64_to_int64 pval state =
  let value = pval |> Float64.to_int64 in
  state |> State.update ~value

let change_int32_to_float64 pval state =
  let value = pval |> Value.Int32.to_float64 in
  state |> State.update ~value

let change_int32_to_int64 pval state =
  let value = pval |> Value.Int32.to_int64 in
  state |> State.update ~value

let change_int64_to_float64 pval state =
  let value = pval |> Value.int64_to_float64 in
  state |> State.update ~value

let change_uint32_to_float64 pval state =
  let value = pval |> Value.cast Type.float64 in
  state |> State.update ~value

let change_uint32_to_uint64 pval state =
  let value = pval |> Value.cast Type.uint64 in
  state |> State.update ~value

let truncate_float64_to_word32 pval state =
  let truncated = pval |> Float64.to_int32 in
  state |> State.update ~value:truncated

let truncate_int64_to_int32 pval state =
  let value = pval |> Value.Int64.to_int32 in
  state |> State.update ~value
