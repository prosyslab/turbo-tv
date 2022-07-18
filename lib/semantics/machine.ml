open Z3utils
module HeapNumber = Objects.HeapNumber
module Composed = Value.Composed
module Repr = MachineType.Repr

(* machine: arithmetic *)

(* assertion:
 * value = ite well-defined FloatAbs(pval) UB *)
let float64_abs vid pval =
  let value = Value.init vid in
  let wd_value = Value.absf pval in
  let assertion = Value.eq value wd_value in
  (value, Control.empty, assertion, Bool.fl, Bool.fl)

(* assertion:
 * value = ite well-defined pval[0:32] UB *)
let float64_extract_high_word32 vid pval =
  let value = Value.init vid in
  let wd_value =
    let hword32 = pval |> Value.data_of |> BitVec.extract 63 32 in
    Value.cast (Type.from_repr Repr.Word32 |> List.hd) hword32
  in
  let assertion = Value.eq value wd_value in
  (value, Control.empty, assertion, Bool.fl, Bool.fl)

(* assertion:
 * value = ite well-defined (lval-rval) UB *)
let float64_sub vid lval rval =
  let value = Value.init vid in
  let wd_value = Value.subf lval rval in
  let assertion = Value.eq value wd_value in
  (value, Control.empty, assertion, Bool.fl, Bool.fl)

(* assertion:
 * value = ite well-defined ((lval+rval) mod 2**32) UB *)
let int32_add vid lval rval =
  let value = Value.init vid in
  let wd_value = Value.Int32.add lval rval in
  let assertion = Value.eq value wd_value in
  (value, Control.empty, assertion, Bool.fl, Bool.fl)

(* assertion:
 * value = ite well-defined ((lval+rval) mod 2**32)::(lval+rval > smi_max) UB *)
let int32_add_with_overflow vid lval rval =
  let value = Composed.init vid 2 in
  let wd_value =
    let added = Value.Int32.add lval rval in
    let res = Value.andi added Constants.int32_mask in
    let ovf =
      Bool.ite (Value.ugti added Constants.int32_mask) Value.tr Value.fl
    in
    Composed.from_values [ res; ovf ]
  in
  let assertion = Value.eq value wd_value in
  (value, Control.empty, assertion, Bool.fl, Bool.fl)

(* assertion:
 *  value = ite well-defined (lval < rval) UB *)
let int32_mul vid lval rval =
  let value = Value.init vid in
  let wd_value = Value.Int32.mul lval rval in
  let assertion = Value.eq value wd_value in
  (value, Control.empty, assertion, Bool.fl, Bool.fl)

(* assertion:
 * value = ite well-defined ((lval-rval) mod 2**32) UB *)
let int32_sub vid lval rval =
  let value = Value.init vid in
  let wd_value = Value.andi (Value.sub lval rval) Constants.smi_mask in
  let assertion = Value.eq value wd_value in
  (value, Control.empty, assertion, Bool.fl, Bool.fl)

(* assertion:
 * value = ite well-defined ((lval+rval) mod 2**64) UB *)
let int64_add vid lval rval =
  let value = Value.init vid in
  let wd_value = Value.add lval rval in
  let assertion = Value.eq value wd_value in
  (value, Control.empty, assertion, Bool.fl, Bool.fl)

(* assertion:
 * value = ite well-defined (lval-rval) UB *)
let int64_sub vid lval rval =
  let value = Value.init vid in
  let wd_value = Value.sub lval rval in
  let assertion = Value.eq value wd_value in
  (value, Control.empty, assertion, Bool.fl, Bool.fl)

(* assertion:
 * value = ite well-defined (Round(lval, rtz)) undefined *)
let round_float64_to_int32 vid pval =
  let value = Value.init vid in
  let wd_value = pval |> Float64.to_int32 in
  let assertion = Value.eq value wd_value in
  (value, Control.empty, assertion, Bool.fl, Bool.fl)

(* well-defined conditions:
 * (hint = "ShiftOutZero" /\ off = (rval mod 32) -> lval[-off:] = 0)
 * assertion:
 * value = ite well-defined (lval >> ((rval mod 32)) UB
 *)
let word32_sar vid hint lval rval =
  let value = Value.init vid in
  let off = Value.modi rval 32 in
  let wd_cond =
    let hint_is_shift_out_zero = String.equal hint "ShfitOutZero" in
    if hint_is_shift_out_zero then
      let shift_out = Value.mask lval off in
      let shift_out_is_zero = Value.eq shift_out Value.zero in
      shift_out_is_zero
    else Bool.tr
  in
  let wd_value = Value.ashr lval off in
  let assertion = Value.eq value wd_value in
  (value, Control.empty, assertion, wd_cond, Bool.fl)

(* assertion:
 * value = ite well-defined (lval << rval) UB *)
let word32_shl vid lval rval =
  let value = Value.init vid in
  let wd_value = Value.shl lval rval in
  let assertion = Value.eq value wd_value in
  (value, Control.empty, assertion, Bool.fl, Bool.fl)

(* assertion:
 * value = ite well-defined (lval >> rval) UB *)
let word32_shr vid lval rval =
  let value = Value.init vid in
  let wd_value = Value.lshr lval rval in
  let assertion = Value.eq value wd_value in
  (value, Control.empty, assertion, Bool.fl, Bool.fl)

(* assertion:
 * value = ite well-defined (lval xor rval) UB *)
let word32_xor vid lval rval =
  let value = Value.init vid in
  let wd_value = Value.xor lval rval in
  let assertion = Value.eq value wd_value in
  (value, Control.empty, assertion, Bool.fl, Bool.fl)

(* assertion:
 * value = ite well-defined (lval << rval) UB *)
let word64_shl vid lval rval =
  let value = Value.init vid in
  let wd_value = Value.shl lval rval in
  let assertion = Value.eq value wd_value in
  (value, Control.empty, assertion, Bool.fl, Bool.fl)

(* machine: logic *)
(* assertion:
 * value = ite well-defined (lval & rval) UB *)
let word32_and vid lval rval =
  let value = Value.init vid in
  let wd_value = Value.and_ lval rval in
  let assertion = Value.eq value wd_value in
  (value, Control.empty, assertion, Bool.fl, Bool.fl)

(* assertion:
 * value = ite well-defined (lval | rval) UB *)
let word32_or vid lval rval =
  let value = Value.init vid in
  let wd_value = Value.or_ lval rval in
  let assertion = Value.eq value wd_value in
  (value, Control.empty, assertion, Bool.fl, Bool.fl)

(* machine: comparison *)
(* assertion:
 *  value = ite well-defined (lval = rval) UB *)
let float64_equal vid lval rval =
  let value = Value.init vid in
  let wd_value = Bool.ite (Float64.eq lval rval) Value.tr Value.fl in
  let assertion = Value.eq value wd_value in
  (value, Control.empty, assertion, Bool.fl, Bool.fl)

(* assertion:
 *  value = ite well-defined (lval < rval) UB *)
let float64_less_than vid lval rval =
  let value = Value.init vid in
  let wd_value = Bool.ite (Float64.lt lval rval) Value.tr Value.fl in
  let assertion = Value.eq value wd_value in
  (value, Control.empty, assertion, Bool.fl, Bool.fl)

(* assertion:
 *  value = ite well-defined (lval <= rval) UB *)
let float64_less_than_or_equal vid lval rval =
  let value = Value.init vid in
  let wd_value = Bool.ite (Float64.le lval rval) Value.tr Value.fl in
  let assertion = Value.eq value wd_value in
  (value, Control.empty, assertion, Bool.fl, Bool.fl)

(* assertion:
 *  value = ite well-defined (lval < rval) UB *)
let int32_less_than vid lval rval =
  let value = Value.init vid in
  let wd_value = Bool.ite (Value.Int32.lt lval rval) Value.tr Value.fl in
  let assertion = Value.eq value wd_value in
  (value, Control.empty, assertion, Bool.fl, Bool.fl)

(* assertion:
 *  value = ite well-defined (lval < rval) UB *)
let int64_less_than vid lval rval =
  let value = Value.init vid in
  let wd_value = Bool.ite (Value.Int64.lt lval rval) Value.tr Value.fl in
  let assertion = Value.eq value wd_value in
  (value, Control.empty, assertion, Bool.fl, Bool.fl)

(* assertion:
 *  value = ite well-defined (lval = rval) UB *)
let word32_equal vid lval rval =
  let value = Value.init vid in
  let wd_value =
    Bool.ite (Value.weak_eq ~repr:Repr.Word32 lval rval) Value.tr Value.fl
  in
  let assertion = Value.eq value wd_value in
  (value, Control.empty, assertion, Bool.fl, Bool.fl)

(* assertion:
 *  value = ite well-defined (lval = rval) UB *)
let word64_equal vid lval rval =
  let value = Value.init vid in
  let wd_value =
    Bool.ite (Value.weak_eq ~repr:Repr.Word64 lval rval) Value.tr Value.fl
  in
  let assertion = Value.eq value wd_value in
  (value, Control.empty, assertion, Bool.fl, Bool.fl)

(* assertion:
 * value = ite well-defined (lval < rval) UB *)
let uint32_less_than vid lval rval =
  let value = Value.init vid in
  let wd_value = Bool.ite (Value.ult lval rval) Value.tr Value.fl in
  let assertion = Value.eq value wd_value in
  (value, Control.empty, assertion, Bool.fl, Bool.fl)

(* assertion:
 * value = ite well-defined (lval <= rval) UB *)
let uint32_less_than_or_equal vid lval rval =
  let value = Value.init vid in
  let wd_value = Bool.ite (Value.ule lval rval) Value.tr Value.fl in
  let assertion = Value.eq value wd_value in
  (value, Control.empty, assertion, Bool.fl, Bool.fl)

(* assertion:
 * value = ite well-defined (lval < rval) UB *)
let uint64_less_than vid lval rval =
  let value = Value.init vid in
  let wd_value = Bool.ite (Value.ult lval rval) Value.tr Value.fl in
  let assertion = Value.eq value wd_value in
  (value, Control.empty, assertion, Bool.fl, Bool.fl)

(* assertion:
 * value = ite well-defined (lval <= rval) UB *)
let uint64_less_than_or_equal vid lval rval =
  let value = Value.init vid in
  let wd_value = Bool.ite (Value.ule lval rval) Value.tr Value.fl in
  let assertion = Value.eq value wd_value in
  (value, Control.empty, assertion, Bool.fl, Bool.fl)

(* machine: memory *)
(* well-defined condition:
 *   IsPointer(ptr) \/
 *   (IsTaggedPointer(ptr) /\ CanAccess(ptr, pos, repr))
 * assertion:
 *   mem = ite well-defined Store(ptr, pos, repr, mem) mem *)
let store ptr pos repr value mem =
  (* ptr must be pointer type & well-defined *)
  let wd_cond =
    (* ptr must be a pointer or tagged pointer *)
    let ptr_is_pointer = Value.has_type Type.pointer ptr in
    let ptr_is_tagged_pointer = Value.has_type Type.tagged_pointer ptr in

    (* check index out-of-bounds *)
    let can_access = TaggedPointer.can_access_as pos repr ptr in

    (* only when value is tagged pointer, check boundary *)
    Bool.ors [ ptr_is_pointer; Bool.ands [ ptr_is_tagged_pointer; can_access ] ]
  in

  let store_size = repr |> Repr.size_of in
  mem :=
    Memory.store
      (ptr |> TaggedPointer.to_raw_pointer)
      store_size wd_cond value !mem;

  (Value.empty, Control.empty, Bool.tr, Bool.fl, Bool.fl)

(* well-defined condition:
 *   IsPointer(ptr) \/
 *   (IsTaggedPointer(ptr) /\ CanAccess(ptr, pos, repr))
 * assertion:
 *   value = (Mem[pos+size]) *)
let load vid ptr pos repr mem =
  let value = Value.init vid in
  let _wd_cond =
    (* ptr must be a pointer or tagged pointer *)
    let ptr_is_pointer = Value.has_type Type.pointer ptr in
    let ptr_is_tagged_pointer = Value.has_type Type.tagged_pointer ptr in

    (* check index out-of-bounds *)
    let can_access = TaggedPointer.can_access_as pos repr ptr in

    (* only when value is tagged pointer, check boundary *)
    Bool.ors [ ptr_is_pointer; Bool.ands [ ptr_is_tagged_pointer; can_access ] ]
  in

  (* Some repr can be mapped to more than one type.
     e.g. Repr.Word8-> [Type.int8; Type.uint8]
     In this case, we pick the head of the type candidates.*)
  let ty = Type.from_repr repr |> List.hd in
  let wd_value =
    Memory.load_as
      (TaggedPointer.move ptr pos |> TaggedPointer.to_raw_pointer)
      repr mem
    |> Value.zero_extend_data |> Value.entype ty
  in
  let assertion = Value.eq value wd_value in
  (value, Control.empty, assertion, Bool.fl, Bool.fl)

(* machine: type-conversion *)
(* assertion:
 * value = ite well-defined int32(v) UB *)
let bitcast_float32_to_int32 vid v =
  let value = Value.init vid in
  let wd_value = v |> Value.cast Type.int32 in
  let assertion = Value.eq value wd_value in
  (value, Control.empty, assertion, Bool.fl, Bool.fl)

(* assertion:
 * value = ite well-defined int64(v) UB *)
let bitcast_float64_to_int64 vid v =
  let value = Value.init vid in
  let wd_value = v |> Value.cast Type.int64 in
  let assertion = Value.eq value wd_value in
  (value, Control.empty, assertion, Bool.fl, Bool.fl)

(* assertion:
 * value = ite well-defined word(v) UB *)
let bitcast_tagged_to_word vid v =
  let value = Value.init vid in
  let ty = Type.from_repr Repr.Word64 |> List.hd in
  let assertion = Value.eq value (v |> Value.cast ty) in
  (value, Control.empty, assertion, Bool.fl, Bool.fl)

(* assertion:
 *  value = ite well-defined word64(v) UB *)
let bitcast_word32_to_word64 vid v =
  let value = Value.init vid in
  let ty = Type.from_repr Repr.Word64 |> List.hd in
  let assertion = Value.eq value (v |> Value.cast ty) in
  (value, Control.empty, assertion, Bool.fl, Bool.fl)

(* assertion:
 * value = ite well-defined tagged(v) UB *)
let bitcast_word_to_tagged vid v =
  let value = Value.init vid in
  let ty = Type.from_repr Repr.Tagged |> List.hd in
  let assertion = Value.eq value (v |> Value.cast ty) in
  (value, Control.empty, assertion, Bool.fl, Bool.fl)

(* assertion:
 *  value = ite well-defined int64(v) UB *)
let change_float64_to_int64 vid pval =
  let value = Value.init vid in
  let wd_value = pval |> Float64.to_int64 in
  let assertion = Value.eq value wd_value in
  (value, Control.empty, assertion, Bool.fl, Bool.fl)

(* assertion:
 *  value = Float64(v) *)
let change_int32_to_float64 vid pval =
  let value = Value.init vid in
  let wd_value = pval |> Value.Int32.to_float64 in
  let assertion = Value.eq value wd_value in
  (value, Control.empty, assertion, Bool.fl, Bool.fl)

(* assertion:
 *  value = Int64(v) *)
let change_int32_to_int64 vid pval =
  let value = Value.init vid in
  let wd_value = pval |> Value.Int32.to_int64 in
  let assertion = Value.eq value wd_value in
  (value, Control.empty, assertion, Bool.fl, Bool.fl)

(* assertion:
 *  value = Float64(v) *)
let change_int64_to_float64 vid pval =
  let value = Value.init vid in
  let wd_value = pval |> Value.int64_to_float64 in
  let assertion = Value.eq value wd_value in
  (value, Control.empty, assertion, Bool.fl, Bool.fl)

(* assertion:
 *  value = ite well-defined float64(v) UB *)
let change_uint32_to_float64 vid pval =
  let value = Value.init vid in
  let wd_value = pval |> Value.cast Type.float64 in
  let assertion = Value.eq value wd_value in
  (value, Control.empty, assertion, Bool.fl, Bool.fl)

(* assertion:
 *  value = ite well-defined uint64(v) UB *)
let change_uint32_to_uint64 vid pval =
  let value = Value.init vid in
  let wd_value = pval |> Value.cast Type.uint64 in
  let assertion = Value.eq value wd_value in
  (value, Control.empty, assertion, Bool.fl, Bool.fl)

(* assertion:
 * value = ite well-defined int32(v) UB *)
let truncate_int64_to_int32 vid pval =
  let value = Value.init vid in
  let wd_value = Value.maski pval 32 |> Value.cast Type.int32 in
  let assertion = Value.eq value wd_value in
  (value, Control.empty, assertion, Bool.fl, Bool.fl)
