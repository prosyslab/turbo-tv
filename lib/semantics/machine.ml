open Z3utils
module HeapNumber = Objects.HeapNumber
module Composed = Value.Composed
module Repr = MachineType.Repr

(* machine: arithmetic *)

(* well-defined condition:
 * - IsFloat64Type(pval)
 * - IsWellDefined(pval)
 * assertion:
 * value = ite well-defined FloatAbs(pval) UB *)
let float64_abs vid pval =
  let value = Value.init vid in
  let wd_cond = Bool.ands [ Value.has_type Type.float64 pval ] in
  let wd_value = Value.absf pval in
  let assertion = Value.eq value wd_value in
  (value, Control.empty, assertion, Bool.not wd_cond)

(* well-defined condition:
 * - IsFloat64Type(pval) 
 * - IsWellDefined(pval) 
 * assertion:
 * value = ite well-defined pval[0:32] UB *)
let float64_extract_high_word32 vid pval =
  let value = Value.init vid in
  let wd_cond = Bool.ands [ Value.has_type Type.float64 pval ] in
  let wd_value =
    let hword32 = pval |> Value.data_of |> BitVec.extract 63 32 in
    Value.cast (Type.from_repr Repr.Word32 |> List.hd) hword32
  in
  let assertion = Value.eq value wd_value in
  (value, Control.empty, assertion, Bool.not wd_cond)

(* well-defined condition:
 * - IsFloat64Type(lval) /\ IsFloat64Type(rval)
 * - IsWellDefined(lval) /\ IsWellDefined(rval)
 * assertion:
 * value = ite well-defined (lval-rval) UB *)
let float64_sub vid lval rval =
  let value = Value.init vid in
  let wd_cond =
    let type_is_float64 =
      Bool.ands
        [ Value.has_type Type.float64 lval; Value.has_type Type.float64 rval ]
    in
    Bool.ands [ type_is_float64 ]
  in
  let wd_value = Value.subf lval rval in
  let assertion = Value.eq value wd_value in
  (value, Control.empty, assertion, Bool.not wd_cond)

(* well-defined condition: 
 * - int32(lval) ^ int32(rval)
 * - well_defined(lval) ^ well_defined(rval)
 * assertion:
 * value = ite well-defined ((lval+rval) mod 2**32) UB *)
let int32_add vid lval rval =
  let value = Value.init vid in
  let wd_cond =
    Bool.ands [ Value.has_type Type.int32 lval; Value.has_type Type.int32 rval ]
  in

  let wd_value = Value.Int32.add lval rval in
  let assertion = Value.eq value wd_value in
  (value, Control.empty, assertion, Bool.not wd_cond)

(* well-defined condition:
 * - int32(lval) ^ int32(rval)
 * - well_defined(lval) ^ well_defined(rval)
 * assertion: 
 * value = ite well-defined ((lval+rval) mod 2**32)::(lval+rval > smi_max) UB *)
let int32_add_with_overflow vid lval rval =
  let value = Composed.init vid 2 in
  let wd_cond =
    let type_is_int32 =
      Bool.ands
        [ Value.has_type Type.int32 lval; Value.has_type Type.int32 rval ]
    in
    Bool.ands [ type_is_int32 ]
  in
  let wd_value =
    let added = Value.Int32.add lval rval in
    let res = Value.andi added Constants.int32_mask in
    let ovf =
      Bool.ite (Value.ugti added Constants.int32_mask) Value.tr Value.fl
    in
    Composed.from_values [ res; ovf ]
  in

  let assertion = Value.eq value wd_value in
  (value, Control.empty, assertion, Bool.not wd_cond)

(* well-defined condition:
 * - is_defined(lval) /\ is_defined(rval)
 * - has_type(lval, int32) ^ has_repr(rval, int32)
 * assertion:
 *  value = ite well-defined (lval < rval) UB *)
let int32_mul vid lval rval =
  let value = Value.init vid in
  let wd_cond =
    let are_int32 =
      Bool.ands
        [ Value.has_type Type.int32 lval; Value.has_type Type.int32 rval ]
    in
    Bool.ands [ are_int32 ]
  in
  let wd_value = Value.Int32.mul lval rval in
  let assertion = Value.eq value wd_value in
  (value, Control.empty, assertion, Bool.not wd_cond)

(* well-defined condition:
 * - int32(lval) ^ int32(rval)
 * - well_defined(lval) ^ well_defined(rval)
 * assertion:
 * value = ite well-defined ((lval-rval) mod 2**32) UB *)
let int32_sub vid lval rval =
  let value = Value.init vid in
  let wd_cond =
    let type_is_int32 =
      Bool.ands
        [ Value.has_type Type.int32 lval; Value.has_type Type.int32 rval ]
    in

    Bool.ands [ type_is_int32 ]
  in
  let wd_value = Value.andi (Value.sub lval rval) Constants.smi_mask in
  let assertion = Value.eq value wd_value in
  (value, Control.empty, assertion, Bool.not wd_cond)

(* well-defined condition:
 * - int64(lval) ^ int64(rval)
 * - well_defined(lval) ^ well_defined(rval)
 * assertion: 
 * value = ite well-defined ((lval+rval) mod 2**64) UB *)
let int64_add vid lval rval =
  let value = Value.init vid in
  let wd_cond =
    let type_is_int64 =
      Bool.ands
        [ Value.has_type Type.int64 lval; Value.has_type Type.int64 rval ]
    in

    Bool.ands [ type_is_int64 ]
  in
  let wd_value = Value.add lval rval in
  let assertion = Value.eq value wd_value in
  (value, Control.empty, assertion, Bool.not wd_cond)

(* Well-defined condition:
 * - int64(lval) ^ int64(rval)
 * - well_defined(lval) ^ well_defined(rval)
 * assertion: 
 * value = ite well-defined (lval-rval) UB *)
let int64_sub vid lval rval =
  let value = Value.init vid in
  let wd_cond =
    let type_is_int64 =
      Bool.ands
        [ Value.has_type Type.int64 lval; Value.has_type Type.int64 rval ]
    in
    Bool.ands [ type_is_int64 ]
  in
  let wd_value = Value.sub lval rval in
  let assertion = Value.eq value wd_value in
  (value, Control.empty, assertion, Bool.not wd_cond)

(* - Well-defined condition = 
 *    IsWellDefined(lval) /\ IsFloat64(lval)
 * - Assertion:
 *     value = ite well-defined (Round(lval, rtz)) undefined *)
let round_float64_to_int32 vid pval =
  let value = Value.init vid in
  let wd_cond = Bool.ands [ Value.has_type Type.float64 pval ] in
  let wd_value = value |> Float64.to_int32 in
  let assertion = Value.eq value wd_value in
  (value, Control.empty, assertion, Bool.not wd_cond)

(* well-defined conditions:
 *  IsWellDefined(lval) /\ IsWellDefined(rval)
 *  /\ HasRepr(lval, Word32) /\ HasRepr(rval, Word32)
 *  /\ (hint = "ShiftOutZero" /\ off = (rval mod 32) -> lval[-off:] = 0)
 * assertion:
 * value = ite well-defined (lval >> ((rval mod 32)) UB 
 *)
let word32_sar vid hint lval rval =
  let value = Value.init vid in
  let off = Value.modi rval 32 in
  let wd_cond =
    let repr_is_word32 =
      Bool.ands
        [ Value.has_repr Repr.Word32 lval; Value.has_repr Repr.Word32 lval ]
    in
    let hint_is_shift_out_zero = String.equal hint "ShfitOutZero" in
    if hint_is_shift_out_zero then
      let shift_out = Value.mask lval off in
      let shift_out_is_zero = Value.eq shift_out Value.zero in
      Bool.ands [ repr_is_word32; shift_out_is_zero ]
    else Bool.ands [ repr_is_word32 ]
  in
  let wd_value = Value.ashr lval off in
  let assertion = Value.eq value wd_value in
  (value, Control.empty, assertion, Bool.not wd_cond)

(* well-defined conditions:
 * - IsWellDefined(lval) ^ IsWellDefined(rval)
 * - HasRepr(lval, Word32) ^ HasRepr(rval, Word32)
 * assertion:
 * value = ite well-defined (lval << rval) UB *)
let word32_shl vid lval rval =
  let value = Value.init vid in
  let wd_cond =
    Bool.ands
      [ Value.has_repr Repr.Word32 lval; Value.has_repr Repr.Word32 rval ]
  in
  let wd_value = Value.shl lval rval in
  let assertion = Value.eq value wd_value in
  (value, Control.empty, assertion, Bool.not wd_cond)

(* well-defined conditions:
 * - IsWellDefined(lval) ^ IsWellDefined(rval)
 * - HasRepr(lval, Word32) ^ HasRepr(rval, Word32)
 * assertion:
 * value = ite well-defined (lval xor rval) UB *)
let word32_xor vid lval rval =
  let value = Value.init vid in
  let wd_cond =
    Bool.ands
      [ Value.has_repr Repr.Word32 lval; Value.has_repr Repr.Word32 rval ]
  in
  let wd_value = Value.xor lval rval in
  let assertion = Value.eq value wd_value in
  (value, Control.empty, assertion, Bool.not wd_cond)

(* well-defined conditions:
 * - IsWellDefined(lval) ^ IsWellDefined(rval)
 * - HasRepr(lval, Word64) ^ HasRepr(rval, Word64)
 * assertion:
 * value = ite well-defined (lval << rval) UB *)
let word64_shl vid lval rval =
  let value = Value.init vid in
  let wd_cond =
    Bool.ands
      [ Value.has_repr Repr.Word64 lval; Value.has_repr Repr.Word64 rval ]
  in
  let wd_value = Value.shl lval rval in
  let assertion = Value.eq value wd_value in
  (value, Control.empty, assertion, Bool.not wd_cond)

(* machine: logic *)
(* well-defined condition:
 * - well_defined(lval) ^ well_defined(rval)
 * - word32(lval) ^ word32(rval)
 * assertion:
 * value = ite well-defined (lval & rval) UB *)
let word32_and vid lval rval =
  let value = Value.init vid in
  let wd_cond =
    let repr_is_word32 =
      Bool.ands
        [ Value.has_repr Repr.Word32 lval; Value.has_repr Repr.Word32 rval ]
    in
    Bool.ands [ repr_is_word32 ]
  in
  let wd_value = Value.and_ lval rval in
  let assertion = Value.eq value wd_value in
  (value, Control.empty, assertion, Bool.not wd_cond)

(* well-defined condition:
 * - IsWellDefined(lval) ^ IsWellDefined(rval)
 * - HasRepr(lval, Word32) ^ HasRepr(rval, Word32)
 * assertion:
 * value = ite well-defined (lval | rval) UB *)
let word32_or vid lval rval =
  let value = Value.init vid in
  let wd_cond =
    Bool.ands
      [ Value.has_repr Repr.Word32 lval; Value.has_repr Repr.Word32 rval ]
  in
  let wd_value = Value.or_ lval rval in
  let assertion = Value.eq value wd_value in
  (value, Control.empty, assertion, Bool.not wd_cond)

(* machine: comparison *)
(* well-defined condition:
 * - has_repr(lval, float64) ^ has_repr(rval, float64)
 * assertion: 
 *  value = ite well-defined (lval = rval) UB *)
let float64_equal vid lval rval =
  let value = Value.init vid in
  let wd_cond =
    Bool.ands
      [ Value.has_repr Repr.Float64 lval; Value.has_repr Repr.Float64 rval ]
  in
  (* use strong equal since only Float64 type is defined for Float64 Repr. *)
  let wd_value = Bool.ite (Float64.eq lval rval) Value.tr Value.fl in
  let assertion = Value.eq value wd_value in
  (value, Control.empty, assertion, Bool.not wd_cond)

(* well-defined condition:
 * - is_defined(lval) /\ is_defined(rval)
 * - has_type(lval, float64) ^ has_type(rval, float64)
 * assertion: 
 *  value = ite well-defined (lval < rval) UB *)
let float64_less_than vid lval rval =
  let value = Value.init vid in
  let wd_cond =
    let are_float64 =
      Bool.ands
        [ Value.has_type Type.float64 lval; Value.has_type Type.float64 rval ]
    in
    Bool.ands [ are_float64 ]
  in
  let wd_value = Bool.ite (Float64.lt lval rval) Value.tr Value.fl in
  let assertion = Value.eq value wd_value in
  (value, Control.empty, assertion, Bool.not wd_cond)

(* well-defined condition:
 * - IsDefined(lval) /\ IsDefined(rval)
 * - IsFloat64(lval) /\ IsFloat64(rval)
 * assertion: 
 *  value = ite well-defined (lval <= rval) UB *)
let float64_less_than_or_equal vid lval rval =
  let value = Value.init vid in
  let wd_cond =
    let are_float64 =
      Bool.ands
        [ Value.has_type Type.float64 lval; Value.has_type Type.float64 rval ]
    in
    Bool.ands [ are_float64 ]
  in
  let wd_value = Bool.ite (Float64.le lval rval) Value.tr Value.fl in
  let assertion = Value.eq value wd_value in
  (value, Control.empty, assertion, Bool.not wd_cond)

(* well-defined condition:
 * - is_defined(lval) /\ is_defined(rval)
 * - has_type(lval, int32) /\ has_repr(rval, int32)
 * assertion:
 *  value = ite well-defined (lval < rval) UB *)
let int32_less_than vid lval rval =
  let value = Value.init vid in
  let wd_cond =
    let are_int32 =
      Bool.ands
        [ Value.has_type Type.int32 lval; Value.has_type Type.int32 rval ]
    in
    Bool.ands [ are_int32 ]
  in
  let wd_value = Bool.ite (Value.Int32.lt lval rval) Value.tr Value.fl in
  let assertion = Value.eq value wd_value in
  (value, Control.empty, assertion, Bool.not wd_cond)

(* well-defined condition:
 * - is_defined(lval) /\ is_defined(rval)
 * - has_type(lval, int64) /\ has_repr(rval, int64)
 * assertion:
 *  value = ite well-defined (lval < rval) UB *)
let int64_less_than vid lval rval =
  let value = Value.init vid in
  let wd_cond =
    let are_int64 =
      Bool.ands
        [ Value.has_type Type.int64 lval; Value.has_type Type.int64 rval ]
    in
    Bool.ands [ are_int64 ]
  in
  let wd_value = Bool.ite (Value.Int64.lt lval rval) Value.tr Value.fl in
  let assertion = Value.eq value wd_value in
  (value, Control.empty, assertion, Bool.not wd_cond)

(* well-defined condition:
 *  IsWellDefined(lval) ^ IsWellDefined(rval)
 * assertion: 
 *  value = ite well-defined (lval = rval) UB *)
let word32_equal vid lval rval =
  let value = Value.init vid in
  let wd_value =
    Bool.ite (Value.weak_eq ~repr:Repr.Word32 lval rval) Value.tr Value.fl
  in
  let assertion = Value.eq value wd_value in
  (value, Control.empty, assertion, Bool.fl)

(* well-defined condition:
 *  IsWellDefined(lval) ^ IsWellDefined(rval) 
 * assertion:
 *  value = ite well-defined (lval = rval) UB *)
let word64_equal vid lval rval =
  let value = Value.init vid in
  let wd_value =
    Bool.ite (Value.weak_eq ~repr:Repr.Word64 lval rval) Value.tr Value.fl
  in
  let assertion = Value.eq value wd_value in
  (value, Control.empty, assertion, Bool.fl)

(* well-defined condition:
 * - IsWellDefined(lval) ^ IsWellDefined(rval)
 * - IsUint32(lval) ^ IsUint32(rval)
 * assertion:
 * value = ite well-defined (lval < rval) UB *)
let uint32_less_than vid lval rval =
  let value = Value.init vid in
  let wd_cond =
    Bool.ands
      [ Value.has_type Type.uint32 lval; Value.has_type Type.uint32 rval ]
  in
  let wd_value = Bool.ite (Value.ult lval rval) Value.tr Value.fl in
  let assertion = Value.eq value wd_value in
  (value, Control.empty, assertion, Bool.not wd_cond)

(* well-defined condition:
 * - IsWellDefined(lval) ^ IsWellDefined(rval)
 * - IsUint32(lval) ^ IsUint32(rval)
 * assertion:
 * value = ite well-defined (lval <= rval) UB *)
let uint32_less_than_or_equal vid lval rval =
  let value = Value.init vid in
  let wd_cond =
    Bool.ands
      [ Value.has_type Type.uint32 lval; Value.has_type Type.uint32 rval ]
  in
  let wd_value = Bool.ite (Value.ule lval rval) Value.tr Value.fl in
  let assertion = Value.eq value wd_value in
  (value, Control.empty, assertion, Bool.not wd_cond)

(* well-defined condition:
 * - well_defined(lval) ^ well_defined(rval)
 * - uint64(lval) ^ uint64(rval)
 * assertion: 
 * value = ite well-defined (lval < rval) UB *)
let uint64_less_than vid lval rval =
  let value = Value.init vid in
  let wd_cond =
    let type_is_uint64 =
      Bool.ands
        [ Value.has_type Type.uint64 lval; Value.has_type Type.uint64 rval ]
    in
    Bool.ands [ type_is_uint64 ]
  in
  let wd_value = Bool.ite (Value.ult lval rval) Value.tr Value.fl in
  let assertion = Value.eq value wd_value in
  (value, Control.empty, assertion, Bool.not wd_cond)

(* well-defined condition:
 * - IsWellDefined(lval) ^ IsWellDefined(rval)
 * - IsUint64(lval) ^ IsUint64(rval)
 * assertion:
 * value = ite well-defined (lval <= rval) UB *)
let uint64_less_than_or_equal vid lval rval =
  let value = Value.init vid in
  let wd_cond =
    Bool.ands
      [ Value.has_type Type.uint64 lval; Value.has_type Type.uint64 rval ]
  in
  let wd_value = Bool.ite (Value.ule lval rval) Value.tr Value.fl in
  let assertion = Value.eq value wd_value in
  (value, Control.empty, assertion, Bool.not wd_cond)

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

  (Value.empty, Control.empty, Bool.tr, Bool.not wd_cond)

(* well-defined condition:
 *   IsPointer(ptr) \/
 *   (IsTaggedPointer(ptr) /\ CanAccess(ptr, pos, repr))
 * assertion:
 *   value = (Mem[pos+size]) *)
let load vid ptr pos repr mem =
  let value = Value.init vid in
  let wd_cond =
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
  (value, Control.empty, assertion, Bool.not wd_cond)

(* machine: type-conversion *)
(* well-defined condition:
 * - well_defined(v) ^ float32(v)
 * assertion:
 * value = ite well-defined int32(v) UB *)
let bitcast_float32_to_int32 vid v =
  let value = Value.init vid in
  let wd_cond = Bool.ands [ Value.has_type Type.float32 v ] in
  let wd_value = v |> Value.cast Type.int32 in
  let assertion = Value.eq value wd_value in
  (value, Control.empty, assertion, Bool.not wd_cond)

(* well-defined condition:
 * - well_defined(v) ^ float64(v)
 * assertion:
 * value = ite well-defined int64(v) UB *)
let bitcast_float64_to_int64 vid v =
  let value = Value.init vid in
  let wd_cond = Bool.ands [ Value.has_type Type.float64 v ] in
  let wd_value = v |> Value.cast Type.int64 in
  let assertion = Value.eq value wd_value in
  (value, Control.empty, assertion, Bool.not wd_cond)

(* well-defined condition:
 * - well_defined(v) ^ tagged(v)
 * assertion:
 * value = ite well-defined word(v) UB *)
let bitcast_tagged_to_word vid v =
  let value = Value.init vid in
  let wd_cond = Bool.ands [ Value.has_type Type.any_tagged v ] in
  let ty = Type.from_repr Repr.Word64 |> List.hd in
  let assertion = Value.eq value (v |> Value.cast ty) in
  (value, Control.empty, assertion, Bool.not wd_cond)

(* well-defined condition:
 *  IsWellDefined(v) /\ HasRepr(v, Word32)
 * assertion:
 *  value = ite well-defined word64(v) UB *)
let bitcast_word32_to_word64 vid v =
  let value = Value.init vid in
  let wd_cond = Bool.ands [ Value.has_repr Repr.Word32 v ] in
  let ty = Type.from_repr Repr.Word64 |> List.hd in
  let assertion = Value.eq value (v |> Value.cast ty) in
  (value, Control.empty, assertion, Bool.not wd_cond)

(* well-defined condition:
 *  IsWellDefined(v) /\ HasRepr(v, Word64)
 * assertion:
 * value = ite well-defined tagged(v) UB *)
let bitcast_word_to_tagged vid v =
  let value = Value.init vid in
  let wd_cond = Bool.ands [ Value.has_repr Repr.Word64 v ] in
  let ty = Type.from_repr Repr.Tagged |> List.hd in
  let assertion = Value.eq value (v |> Value.cast ty) in
  (value, Control.empty, assertion, Bool.not wd_cond)

(* well-defined condition:
 * - well_defined(v) ^ float64(v)
 * assertion:
 *  value = ite well-defined int64(v) UB *)
let change_float64_to_int64 vid pval =
  let value = Value.init vid in
  let wd_cond = Bool.ands [ Value.has_type Type.float64 pval ] in
  let wd_value = value |> Float64.to_int64 in
  let assertion = Value.eq value wd_value in
  (value, Control.empty, assertion, Bool.not wd_cond)

(* well-defined condition:
 *  IsInt32(v)
 * assertion:
 *  value = Float64(v) *)
let change_int32_to_float64 vid pval =
  let value = Value.init vid in
  let wd_cond = Value.has_type Type.int32 pval in
  let wd_value = value |> Value.Int32.to_float64 in
  let assertion = Value.eq value wd_value in
  (value, Control.empty, assertion, Bool.not wd_cond)

(* well-defined condition:
 *  IsInt32(v)
 * assertion:
 *  value = Int64(v) *)
let change_int32_to_int64 vid pval =
  let value = Value.init vid in
  let wd_cond = Value.has_type Type.int32 pval in
  (* extend sign bit *)
  let wd_value = value |> Value.Int32.to_int64 in
  let assertion = Value.eq value wd_value in
  (value, Control.empty, assertion, Bool.not wd_cond)

(* well-defined condition:
 *  IsInt64(v)
 * assertion:
 *  value = Float64(v) *)
let change_int64_to_float64 vid pval =
  let value = Value.init vid in
  let wd_cond = Value.has_type Type.int64 pval in
  let wd_value = value |> Value.int64_to_float64 in
  let assertion = Value.eq value wd_value in
  (value, Control.empty, assertion, Bool.not wd_cond)

(* well-defined condition:
 * - well_defined(v) ^ uint32(v)
 * assertion:
 *  value = ite well-defined float64(v) UB *)
let change_uint32_to_float64 vid pval =
  let value = Value.init vid in
  let wd_cond = Bool.ands [ Value.has_type Type.uint32 pval ] in
  let wd_value = value |> Value.cast Type.float64 in
  let assertion = Value.eq value wd_value in
  (value, Control.empty, assertion, Bool.not wd_cond)

(* well-defined condition:
 * - well_defined(v) ^ uint32(v)
 * assertion:
 *  value = ite well-defined uint64(v) UB *)
let change_uint32_to_uint64 vid pval =
  let value = Value.init vid in
  let wd_cond = Bool.ands [ Value.has_type Type.uint32 pval ] in
  let wd_value = value |> Value.cast Type.uint64 in
  let assertion = Value.eq value wd_value in
  (value, Control.empty, assertion, Bool.not wd_cond)

(* well-defined condition:
 * - well_defined(v) ^ int64(v)
 * assertion:
 * value = ite well-defined int32(v) UB *)
let truncate_int64_to_int32 vid v =
  let value = Value.init vid in
  let wd_cond = Bool.ands [ Value.has_type Type.int64 v ] in
  let wd_value = Value.maski v 32 |> Value.cast Type.int32 in
  let assertion = Value.eq value wd_value in
  (value, Control.empty, assertion, Bool.not wd_cond)
