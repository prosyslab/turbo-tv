open Z3utils
module HeapNumber = Objects.HeapNumber
module Composed = Value.Composed
module Repr = MachineType.Repr

(* machine: arithmetic *)
(* well-defined condition: 
 * - int32(lval) ^ int32(rval)
 * - well_defined(lval) ^ well_defined(rval)
 * assertion:
 * value = ite well-defined ((lval+rval) mod 2**32) UB *)
let int32add vid lval rval =
  let value = Value.init vid in
  let wd_cond =
    let type_is_int32 =
      Bool.ands
        [ Value.has_type Type.int32 lval; Value.has_type Type.int32 rval ]
    in
    let is_well_defined =
      Bool.ands [ Value.is_defined lval; Value.is_defined rval ]
    in
    Bool.ands [ type_is_int32; is_well_defined ]
  in
  let wd_value = Value.andi (Value.add lval rval) Constants.smi_mask in
  let assertion = Value.eq value (Bool.ite wd_cond wd_value Value.undefined) in
  (value, Control.empty, assertion, Bool.fl)

(* well-defined condition:
 * - int32(lval) ^ int32(rval)
 * - well_defined(lval) ^ well_defined(rval)
 * assertion: 
 * value = ite well-defined ((lval+rval) mod 2**32)::(lval+rval > smi_max) UB *)
let int32add_with_overflow vid lval rval =
  let value = Composed.init vid 2 in
  let wd_cond =
    let type_is_int32 =
      Bool.ands
        [ Value.has_type Type.int32 lval; Value.has_type Type.int32 rval ]
    in
    let is_well_defined =
      Bool.ands [ Value.is_defined lval; Value.is_defined rval ]
    in
    Bool.ands [ type_is_int32; is_well_defined ]
  in
  let wd_value =
    let added = Value.add lval rval in
    let res = Value.andi added Constants.smi_mask in
    let ovf = Bool.ite (Value.ugti added Constants.smi_max) Value.tr Value.fl in
    Composed.from_values [ res; ovf ]
  in
  let ud_value = Composed.from_values [ Value.undefined; Value.undefined ] in

  let assertion = Value.eq value (Bool.ite wd_cond wd_value ud_value) in
  (value, Control.empty, assertion, Bool.fl)

(* well-defined condition:
 * - int64(lval) ^ int64(rval)
 * - well_defined(lval) ^ well_defined(rval)
 * assertion: 
 * value = ite well-defined ((lval+rval) mod 2**64) UB *)
let int64add vid lval rval =
  let value = Value.init vid in
  let wd_cond =
    let type_is_int64 =
      Bool.ands
        [ Value.has_type Type.int64 lval; Value.has_type Type.int64 rval ]
    in
    let is_well_defined =
      Bool.ands [ Value.is_defined lval; Value.is_defined rval ]
    in
    Bool.ands [ type_is_int64; is_well_defined ]
  in
  let wd_value = Value.add lval rval in
  let assertion = Value.eq value (Bool.ite wd_cond wd_value Value.undefined) in
  (value, Control.empty, assertion, Bool.fl)

(* Well-defined condition:
 * - int64(lval) ^ int64(rval)
 * - well_defined(lval) ^ well_defined(rval)
 * assertion: 
 * value = ite well-defined (lval-rval) UB *)
let int64sub vid lval rval =
  let value = Value.init vid in
  let wd_cond =
    let type_is_int64 =
      Bool.ands
        [ Value.has_type Type.int64 lval; Value.has_type Type.int64 rval ]
    in
    let is_well_defined =
      Bool.ands [ Value.is_defined lval; Value.is_defined rval ]
    in
    Bool.ands [ type_is_int64; is_well_defined ]
  in
  let wd_value = Value.sub lval rval in
  let assertion = Value.eq value (Bool.ite wd_cond wd_value Value.undefined) in
  (value, Control.empty, assertion, Bool.fl)

(* - Well-defined condition = 
 *    WellDefined(lval) /\ IsFloat64(lval)
 * - Assertion:
 *     value = ite well-defined (Round(lval, rtz)) undefined *)
let round_float64_to_int32 vid pval =
  let value = Value.init vid in
  let wd_cond =
    Bool.ands [ Value.is_defined pval; Value.has_type Type.float64 pval ]
  in
  let wd_value = value |> Value.round_float64_to_int32 in
  let assertion = Value.eq value (Bool.ite wd_cond wd_value Value.undefined) in
  (value, Control.empty, assertion, Bool.fl)

(* well-defined conditions:
 * - well_defined(lval) ^ well_defined(rval)
 * - word32(lval) ^ word32(rval)
 * - hint = "ShiftOutZero" ^ off = (rval mod 32) -> lval[-off:] = 0
 * assertion:
 * value = ite well-defined (lval >> ((rval mod 32)) UB 
 *)
let word32sar vid hint lval rval =
  let value = Value.init vid in
  let off = Value.modi rval 32 in
  let wd_cond =
    let is_well_defined =
      Bool.ands [ Value.is_defined lval; Value.is_defined rval ]
    in
    let repr_is_word32 =
      Bool.ands
        [ Value.has_repr Repr.Word32 lval; Value.has_repr Repr.Word32 lval ]
    in
    let hint_is_shift_out_zero = String.equal hint "ShfitOutZero" in
    if hint_is_shift_out_zero then
      let shift_out = Value.mask lval off in
      let shift_out_is_zero = Value.eq shift_out Value.zero in
      Bool.ands [ is_well_defined; repr_is_word32; shift_out_is_zero ]
    else Bool.ands [ is_well_defined; repr_is_word32 ]
  in
  let wd_value = Value.ashr lval off in
  let assertion = Value.eq value (Bool.ite wd_cond wd_value Value.undefined) in
  (value, Control.empty, assertion, Bool.fl)

(* well-defined conditions:
 * - well_defined(lval) ^ well_defined(rval)
 * - word64(lval) ^ word64(rval)
 * assertion:
 * value = ite well-defined (lval >> rval) UB *)
let word64shl vid lval rval =
  let value = Value.init vid in
  let wd_cond =
    let is_well_defined =
      Bool.ands [ Value.is_defined lval; Value.is_defined rval ]
    in
    let repr_is_word64 =
      Bool.ands
        [ Value.has_repr Repr.Word64 lval; Value.has_repr Repr.Word64 lval ]
    in
    Bool.ands [ is_well_defined; repr_is_word64 ]
  in
  let wd_value = Value.shl lval rval in
  let assertion = Value.eq value (Bool.ite wd_cond wd_value Value.undefined) in
  (value, Control.empty, assertion, Bool.fl)

(* machine: logic *)
(* well-defined condition:
 * - well_defined(lval) ^ well_defined(rval)
 * - word32(lval) ^ word32(rval)
 * assertion:
 * value = ite well-defined (lval & rval) UB *)
let word32and vid lval rval =
  let value = Value.init vid in
  let wd_cond =
    let is_well_defined =
      Bool.ands [ Value.is_defined lval; Value.is_defined rval ]
    in
    let repr_is_word32 =
      Bool.ands
        [ Value.has_repr Repr.Word32 lval; Value.has_repr Repr.Word32 rval ]
    in
    Bool.ands [ is_well_defined; repr_is_word32 ]
  in
  let wd_value = Value.and_ lval rval in
  let assertion = Value.eq value (Bool.ite wd_cond wd_value Value.undefined) in
  (value, Control.empty, assertion, Bool.fl)

(* machine: comparison *)
(* well-defined condition:
 * - has_repr(lval, float64) ^ has_repr(rval, float64)
 * assertion: 
 *  value = ite well-defined (lval = rval) UB *)
let float64equal vid lval rval =
  let value = Value.init vid in
  let wd_cond =
    Bool.ands
      [ Value.has_repr Repr.Float64 lval; Value.has_repr Repr.Float64 rval ]
  in
  (* use strong equal since only Float64 type is defined for Float64 Repr. *)
  let wd_value = Bool.ite (Value.eq lval rval) Value.tr Value.fl in
  let assertion = Value.eq value (Bool.ite wd_cond wd_value Value.undefined) in
  (value, Control.empty, assertion, Bool.fl)

(* well-defined condition:
 * - has_repr(lval, float64) ^ has_repr(rval, float64)
 * assertion: 
 *  value = ite well-defined (lval < rval) UB *)
let float64_less_than vid lval rval =
  let value = Value.init vid in
  let wd_cond =
    Bool.ands
      [ Value.has_repr Repr.Float64 lval; Value.has_repr Repr.Float64 rval ]
  in
  let wd_value = Bool.ite (Value.Float64.lt lval rval) Value.tr Value.fl in
  let assertion = Value.eq value (Bool.ite wd_cond wd_value Value.undefined) in
  (value, Control.empty, assertion, Bool.fl)

(* well-defined condition:
 * - has_repr(lval, word32) ^ has_repr(rval, word32)
 * assertion: 
 *  value = ite well-defined (lval = rval) UB *)
let word32equal vid lval rval =
  let value = Value.init vid in
  let wd_cond =
    Bool.ands
      [ Value.has_repr Repr.Word32 lval; Value.has_repr Repr.Word32 rval ]
  in
  let wd_value = Bool.ite (Value.weak_eq lval rval) Value.tr Value.fl in
  let assertion = Value.eq value (Bool.ite wd_cond wd_value Value.undefined) in
  (value, Control.empty, assertion, Bool.fl)

(* well-defined condition:
 * - has_repr(lval, word64) ^ has_repr(rval, word64)
 * assertion:
 *  value = ite well-defined (lval = rval) UB *)
let word64equal vid lval rval =
  let value = Value.init vid in
  let wd_cond =
    Bool.ands
      [ Value.has_repr Repr.Word64 lval; Value.has_repr Repr.Word64 rval ]
  in
  let wd_value = Bool.ite (Value.weak_eq lval rval) Value.tr Value.fl in
  let assertion = Value.eq value (Bool.ite wd_cond wd_value Value.undefined) in
  (value, Control.empty, assertion, Bool.fl)

(* well-defined condition:
 * - well_defined(lval) ^ well_defined(rval)
 * - uint64(lval) ^ uint64(rval)
 * assertion: 
 * value = ite well-defined (lval < rval) UB *)
let uint64less_than vid lval rval =
  let value = Value.init vid in
  let wd_cond =
    let is_well_defined =
      Bool.ands [ Value.is_defined lval; Value.is_defined rval ]
    in
    let type_is_uint64 =
      Bool.ands
        [ Value.has_type Type.uint64 lval; Value.has_type Type.uint64 rval ]
    in
    Bool.ands [ is_well_defined; type_is_uint64 ]
  in
  let wd_value = Bool.ite (Value.ult lval rval) Value.tr Value.fl in
  let assertion = Value.eq value (Bool.ite wd_cond wd_value Value.undefined) in
  (value, Control.empty, assertion, Bool.fl)

(* machine: memory *)
(* defined condition:
 *   well_defined(ptr) /\ well_defined(pos) /\
 *   pointer(ptr) /\
 *   can_access(ptr, pos, size)
 * behavior:
 *   ite defined (Mem[pos+size] := value) UB
 *)
let store ptr pos repr value mem =
  (* ptr must be pointer type & well-defined *)
  let ptr_is_pointer = Value.has_type Type.pointer ptr in
  let ptr_is_defined = Value.is_defined ptr in
  (* check index out-of-bounds *)
  let pos_is_defined = Value.is_defined pos in
  let can_access = Pointer.can_access_as pos repr ptr in
  let store_cond =
    Bool.ands [ ptr_is_pointer; ptr_is_defined; pos_is_defined; can_access ]
  in
  let ub_cond = Bool.not store_cond in

  let store_size = repr |> Repr.size_of in
  mem := Memory.store ptr store_size store_cond value !mem;

  (Value.empty, Control.empty, Bool.tr, ub_cond)

(* well-defined condition:
 * - well_defined(ptr) ^ well_defined(pos)
 * - pointer(ptr) ^ repr(pos)
 * - can_access(ptr, pos, size)
 * assertion:
 * value = ite well-defined (Mem[pos+size]) UB *)
let load vid ptr pos repr mem =
  let value = Value.init vid in
  let wd_cond =
    (* ptr must be pointer type & well-defined *)
    let ptr_is_pointer = Value.has_type Type.pointer ptr in
    let ptr_is_defined = Value.is_defined ptr in

    (* pos must be well-defined *)
    let pos_is_defined = Value.is_defined pos in

    (* check index out-of-bounds *)
    let no_oob = Pointer.can_access_as pos repr ptr in
    Bool.ands [ ptr_is_pointer; ptr_is_defined; pos_is_defined; no_oob ]
  in

  (* Some repr can be mapped to more than one type.
     e.g. Repr.Word8-> [Type.int8; Type.uint8]
     In this case, we pick the head of the type candidates.*)
  let ty = Type.from_repr repr |> List.hd in
  let wd_value =
    Memory.load_as (Pointer.move ptr pos) repr mem |> Value.entype ty
  in
  let assertion = Value.eq value (Bool.ite wd_cond wd_value Value.undefined) in
  (value, Control.empty, assertion, Bool.fl)

(* machine: type-conversion *)
(* well-defined condition:
 * - well_defined(v) ^ float32(v)
 * assertion:
 * value = ite well-defined int32(v) UB *)
let bitcast_float32_to_int32 vid v =
  let value = Value.init vid in
  let wd_cond =
    Bool.ands [ Value.is_defined v; Value.has_type Type.float32 v ]
  in
  let wd_value = v |> Value.cast Type.int32 in
  let assertion = Value.eq value (Bool.ite wd_cond wd_value Value.undefined) in
  (value, Control.empty, assertion, Bool.fl)

(* well-defined condition:
 * - well_defined(v) ^ float64(v)
 * assertion:
 * value = ite well-defined int64(v) UB *)
let bitcast_float64_to_int64 vid v =
  let value = Value.init vid in
  let wd_cond =
    Bool.ands [ Value.is_defined v; Value.has_type Type.float64 v ]
  in
  let wd_value = v |> Value.cast Type.int64 in
  let assertion = Value.eq value (Bool.ite wd_cond wd_value Value.undefined) in
  (value, Control.empty, assertion, Bool.fl)

(* well-defined condition:
 * - well_defined(v) ^ tagged(v)
 * assertion:
 * value = ite well-defined word(v) UB *)
let bitcast_tagged_to_word vid v =
  let value = Value.init vid in
  let wd_cond =
    Bool.ands [ Value.is_defined v; Value.has_type Type.any_tagged v ]
  in
  let ty = Type.from_repr Repr.Word64 |> List.hd in
  let assertion =
    Value.eq value (Bool.ite wd_cond (v |> Value.cast ty) Value.undefined)
  in
  (value, Control.empty, assertion, Bool.fl)

(* well-defined condition:
 * - well_defined(v) ^ word32(v)
 * assertion:
 * value = ite well-defined word64(v) UB *)
let bitcast_word32_to_word64 vid v =
  let value = Value.init vid in
  let wd_cond =
    Bool.ands [ Value.is_defined v; Value.has_repr Repr.Word32 v ]
  in
  let ty = Type.from_repr Repr.Word64 |> List.hd in
  let assertion =
    Value.eq value (Bool.ite wd_cond (v |> Value.cast ty) Value.undefined)
  in
  (value, Control.empty, assertion, Bool.fl)

(* well-defined condition:
 * - well_defined(v) ^ any_tagged(v)
 * assertion:
 * value = ite well-defined tagged(v) UB *)
let bitcast_word_to_tagged vid v =
  let value = Value.init vid in
  let wd_cond =
    Bool.ands [ Value.is_defined v; Value.has_repr Repr.Word64 v ]
  in
  let ty = Type.from_repr Repr.Tagged |> List.hd in
  let assertion =
    Value.eq value (Bool.ite wd_cond (v |> Value.cast ty) Value.undefined)
  in
  (value, Control.empty, assertion, Bool.fl)

(* well-defined condition:
 * - well_defined(v) ^ float64(v)
 * assertion:
 *  value = ite well-defined int64(v) UB *)
let change_float64_to_int64 vid pval =
  let value = Value.init vid in
  let wd_cond =
    Bool.ands [ Value.is_defined pval; Value.has_type Type.float64 pval ]
  in
  let wd_value = value |> Value.float64_to_int64 in
  let assertion = Value.eq value (Bool.ite wd_cond wd_value Value.undefined) in
  (value, Control.empty, assertion, Bool.fl)

(* well-defined condition:
 * - well_defined(v) ^ int32(v)
 * assertion:
 *  value = ite well-defined float64(v) UB *)
let change_int32_to_float64 vid pval =
  let value = Value.init vid in
  let wd_cond =
    Bool.ands [ Value.is_defined pval; Value.has_type Type.int32 pval ]
  in
  let wd_value = value |> Value.int32_to_float64 in
  let assertion = Value.eq value (Bool.ite wd_cond wd_value Value.undefined) in
  (value, Control.empty, assertion, Bool.fl)

(* well-defined condition:
 * - well_defined(v) ^ int32(v)
 * assertion:
 *  value = ite well-defined int64(v) UB *)
let change_int32_to_int64 vid pval =
  let value = Value.init vid in
  let wd_cond =
    Bool.ands [ Value.is_defined pval; Value.has_type Type.int32 pval ]
  in
  (* extend sign bit *)
  let wd_value = value |> Value.int32_to_int64 in
  let assertion = Value.eq value (Bool.ite wd_cond wd_value Value.undefined) in
  (value, Control.empty, assertion, Bool.fl)

(* well-defined condition:
 * - well_defined(v) ^ int64(v)
 * assertion:
 *  value = ite well-defined float64(v) UB *)
let change_int64_to_float64 vid pval =
  let value = Value.init vid in
  let wd_cond =
    Bool.ands [ Value.is_defined pval; Value.has_type Type.int64 pval ]
  in
  let wd_value = value |> Value.int64_to_float64 in
  let assertion = Value.eq value (Bool.ite wd_cond wd_value Value.undefined) in
  (value, Control.empty, assertion, Bool.fl)

(* well-defined condition:
 * - well_defined(v) ^ uint32(v)
 * assertion:
 *  value = ite well-defined float64(v) UB *)
let change_uint32_to_float64 vid pval =
  let value = Value.init vid in
  let wd_cond =
    Bool.ands [ Value.is_defined pval; Value.has_type Type.uint32 pval ]
  in
  let wd_value = value |> Value.cast Type.float64 in
  let assertion = Value.eq value (Bool.ite wd_cond wd_value Value.undefined) in
  (value, Control.empty, assertion, Bool.fl)

(* well-defined condition:
 * - well_defined(v) ^ uint32(v)
 * assertion:
 *  value = ite well-defined uint64(v) UB *)
let change_uint32_to_uint64 vid pval =
  let value = Value.init vid in
  let wd_cond =
    Bool.ands [ Value.is_defined pval; Value.has_type Type.uint32 pval ]
  in
  let wd_value = value |> Value.cast Type.uint64 in
  let assertion = Value.eq value (Bool.ite wd_cond wd_value Value.undefined) in
  (value, Control.empty, assertion, Bool.fl)

(* well-defined condition:
 * - well_defined(v) ^ int64(v)
 * assertion:
 * value = ite well-defined int32(v) UB *)
let truncate_int64_to_int32 vid v =
  let value = Value.init vid in
  let wd_cond = Bool.ands [ Value.is_defined v; Value.has_type Type.int64 v ] in
  let wd_value = Value.maski v 32 |> Value.cast Type.int32 in
  let assertion = Value.eq value (Bool.ite wd_cond wd_value Value.undefined) in
  (value, Control.empty, assertion, Bool.fl)
