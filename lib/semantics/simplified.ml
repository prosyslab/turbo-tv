open Z3utils
module HeapNumber = Objects.HeapNumber
module Repr = MachineType.Repr

(* simplified: arithmetic *)
(* well-defined condition:
 * - WellDefined(lval) ^ WellDefined(rval)
 * - IsInt32(lval) ^ IsInt32(rval)
 * | IsInt64(lval) ^ IsInt64(rval)
 * | IsFloat64(lval) ^ IsFloat64(rval)
 * assertion:
 *  value = ite well-defined (lval + rval) UB *)
let number_add vid lval rval =
  let value = Value.init vid in
  let lval_int32 = Value.has_type Type.int32 lval in
  let rval_int32 = Value.has_type Type.int32 rval in
  let lval_int64 = Value.has_type Type.int64 lval in
  let rval_int64 = Value.has_type Type.int64 rval in
  let lval_float64 = Value.has_type Type.float64 lval in
  let rval_float64 = Value.has_type Type.float64 rval in
  let wd_cond =
    Bool.ands
      [
        Value.is_defined lval;
        Value.is_defined rval;
        Bool.ors
          [
            Bool.ands [ lval_int32; rval_int32 ];
            Bool.ands [ lval_int64; rval_int64 ];
            Bool.ands [ lval_float64; rval_float64 ];
          ];
      ]
  in
  let wd_value =
    Bool.ite
      (Bool.ors [ lval_int32; lval_int64 ])
      (Value.add lval rval) (Value.addf lval rval)
  in
  let assertion = Value.eq value (Bool.ite wd_cond wd_value Value.undefined) in
  (value, Control.empty, assertion, Bool.fl)

let number_abs vid pval =
  let value = Value.init vid in
  let wd_cond = Value.is_defined pval in
  let ty = Value.ty_of pval in
  let wd_value =
    Bool.ite
      (Bool.ors
         [ Value.has_type Type.int32 pval; Value.has_type Type.int64 pval ])
      (Value.abs ty pval) (Value.absf pval)
  in
  let assertion = Value.eq value (Bool.ite wd_cond wd_value Value.undefined) in
  (value, Control.empty, assertion, Bool.fl)

(* well-defined condition:
 * - WellDefined(lval) ^ WellDefined(rval)
 * - IsWord32(lval) ^ IsWord32(rval)
 * assertion:
 *  value = ite well-defined (lval xor rval) UB *)
let speculative_number_bitwise_xor vid lval rval =
  let value = Value.init vid in
  let wd_cond =
    Bool.ands
      [
        Value.is_defined lval;
        Value.is_defined rval;
        Value.has_repr Repr.Word32 lval;
        Value.has_repr Repr.Word32 rval;
      ]
  in
  let wd_value = Value.xor lval rval in
  let assertion = Value.eq value (Bool.ite wd_cond wd_value Value.undefined) in
  (value, Control.empty, assertion, Bool.fl)

(* well-defined condition:
 * - IsTaggedPointer(lval) /\ IsTaggedPointer(rval)
 * - PointsNumberObject(lval) /\ PointsNumberObject(rval)
 * - IsSafeInteger(lval) /\ IsSafeInteger(rval)
 * - IsWellDefined(lval) /\ IsWellDefined(rval)
 * assertion:
 *  value = ite well-defined (lval+rval) UB *)
let speculative_safe_integer_add vid lval rval next_bid mem =
  let value = Value.init vid in

  let lnum = HeapNumber.load lval !mem in
  let rnum = HeapNumber.load lval !mem in

  let wd_cond =
    Bool.ands
      [
        Value.is_defined lval;
        Value.is_defined rval;
        lval |> Value.has_type Type.tagged_pointer;
        rval |> Value.has_type Type.tagged_pointer;
        Objects.is_heap_number lval !mem;
        Objects.is_heap_number rval !mem;
        HeapNumber.is_safe_integer lnum;
        HeapNumber.is_safe_integer rnum;
      ]
  in
  let ub_cond = Bool.not wd_cond in

  let res_ptr = HeapNumber.allocate next_bid in
  let res = Value.Float64.add lnum.value rnum.value |> HeapNumber.from_value in
  HeapNumber.store res_ptr res wd_cond mem;

  let wd_value = res_ptr in
  let assertion = Value.eq value (Bool.ite wd_cond wd_value Value.undefined) in

  (value, Control.empty, assertion, ub_cond)

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
  let rnum = HeapNumber.load lval !mem in

  let ub_cond =
    Bool.not
      (Bool.ands
         [
           Value.is_defined lval;
           Value.is_defined rval;
           lval |> Value.has_type Type.tagged_pointer;
           rval |> Value.has_type Type.tagged_pointer;
           Objects.is_heap_number lval !mem;
           Objects.is_heap_number rval !mem;
         ])
  in
  let wd_cond =
    Bool.ands
      [
        Bool.not ub_cond;
        HeapNumber.is_safe_integer lnum;
        HeapNumber.is_safe_integer rnum;
      ]
  in

  let res_ptr = HeapNumber.allocate next_bid in
  let res = Value.Float64.sub lnum.value rnum.value |> HeapNumber.from_value in
  HeapNumber.store res_ptr res wd_cond mem;

  let wd_value = res_ptr in
  let assertion = Value.eq value (Bool.ite wd_cond wd_value Value.undefined) in

  (value, Control.empty, assertion, ub_cond)

let number_expm1 vid nptr next_bid mem =
  let value = Value.init vid in
  let wd_cond =
    Bool.ands
      [
        Value.is_defined nptr;
        nptr |> Value.has_type Type.tagged_pointer;
        Objects.is_heap_number nptr !mem;
      ]
  in
  let ub_cond = Bool.not wd_cond in

  (* expm1 = e^{n}-1 *)
  let res_ptr = HeapNumber.allocate next_bid in
  let expm1 =
    let n = HeapNumber.load nptr !mem in
    let bv_sort = BV.mk_sort ctx 64 in
    let expm_decl =
      Z3.FuncDecl.mk_func_decl_s ctx "unknown_number_expm1" [ bv_sort ] bv_sort
    in
    Bool.ite
      (HeapNumber.is_minus_zero n)
      (BitVecVal.minus_zero ())
      (Bool.ite (HeapNumber.is_inf n) (BitVecVal.inf ())
         (Bool.ite (HeapNumber.is_ninf n)
            (BitVecVal.from_f64string "-1.0")
            (Bool.ite (HeapNumber.is_nan n) (BitVecVal.nan ())
               (Bool.ite (HeapNumber.is_zero n)
                  (BitVecVal.from_f64string "0.0")
                  (Z3.FuncDecl.apply expm_decl [ n.value ])))))
    |> HeapNumber.from_value
  in
  HeapNumber.store res_ptr expm1 wd_cond mem;
  let wd_value = res_ptr in

  let assertion = Value.eq value (Bool.ite wd_cond wd_value Value.undefined) in
  (value, Control.empty, assertion, ub_cond)

(* simplified: comparison *)
(* well-defined condition:
 * - WellDefined(pval) ^ IsBool(pval)
 * assertion:
 *  value = ite well-defined (not pval) UB *)
let boolean_not vid pval =
  let value = Value.init vid in
  let wd_cond =
    Bool.ands [ Value.is_defined pval; Value.has_type Type.bool pval ]
  in
  let assertion =
    Value.eq value (Bool.ite wd_cond (Bool.not pval) Value.undefined)
  in
  (value, Control.empty, assertion, Bool.fl)

(* simplified: memory *)
let allocate_raw vid cid size next_bid ct =
  let value = Value.init vid in
  let control = Control.init cid in
  let pointer = Memory.allocate next_bid size in
  (* assume AllocateRaw doesn't change the control *)
  let assertion = Bool.ands [ Value.eq value pointer; Bool.eq control ct ] in
  (value, control, assertion, Bool.fl)

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
  let can_access = Pointer.can_access_as pos repr ptr in
  let ub_cond = Bool.not (Bool.ands [ ty_check; can_access ]) in
  let store_cond = Bool.not ub_cond in

  mem := Memory.store_as (Pointer.move ptr pos) repr store_cond value !mem;
  (Value.empty, Control.empty, Bool.tr, ub_cond)

(* simplified: type-conversion *)
(* well-defined condition 
 * - IsInt32(pval) /\ IsWellDefined(pval) 
 * - SmiMin < pval < SmiMax
 * assertion:
 * value = ite well-defined TaggedSigned(pval) UV *)
let change_int31_to_taggedsigned vid pval =
  let value = Value.init vid in
  let wd_cond =
    Bool.ands
      [
        pval |> Value.has_type Type.int32;
        Value.is_defined pval;
        Value.Int32.is_in_smi_range pval;
      ]
  in
  let wd_value = Value.Int32.to_tagged_signed pval in
  let assertion = Value.eq value (Bool.ite wd_cond wd_value Value.undefined) in
  (value, Control.empty, assertion, Bool.fl)

(* Well-defined condition =
 *  IsInt32(pval) /\ WellDefined(pval)
 * Assertion =
 *  value = ite well-defined (tagged(pval)) UB *)
let change_int32_to_tagged vid pval next_bid mem =
  let value = Value.init vid in
  let data = Value.data_of pval in

  let wd_cond =
    Bool.ands [ Value.is_defined pval; Value.has_type Type.int32 pval ]
  in

  (* if pval is in smi range, value = TaggedSigned(pval+pval) *)
  let is_in_smi_range = Value.Int32.is_in_smi_range pval in
  let smi = Value.Int32.to_tagged_signed pval in

  let ptr = HeapNumber.allocate next_bid in
  let number_value = data |> Float.from_signed_bv |> Float.to_ieee_bv in
  let obj = HeapNumber.from_value number_value in
  HeapNumber.store ptr obj (Bool.not is_in_smi_range) mem;

  let wd_value = Bool.ite is_in_smi_range smi ptr in
  let assertion = Value.eq value (Bool.ite wd_cond wd_value Value.undefined) in
  (value, Control.empty, assertion, Bool.fl)

(* well-defined condition:
 * - int64(pval) 
 * - WellDefined(lval)
 * assertion:
 *  value = ite well-defined (tagged(pval)) UB *)
let change_int64_to_tagged vid pval next_bid mem =
  let value = Value.init vid in
  let data = Value.data_of value in

  let wd_cond =
    Bool.ands [ Value.is_defined pval; Value.has_type Type.int64 pval ]
  in

  (* if pval is in smi range, value = TaggedSigned(pval+pval) *)
  let is_in_smi_range = Value.Int64.is_in_smi_range pval in
  let smi = Value.Int64.to_tagged_signed pval in

  let ptr = HeapNumber.allocate next_bid in
  let number_value = data |> Float.from_signed_bv |> Float.to_ieee_bv in
  let obj = HeapNumber.from_value number_value in
  HeapNumber.store ptr obj (Bool.not is_in_smi_range) mem;

  let wd_value = Bool.ite is_in_smi_range smi ptr in
  let assertion = Value.eq value (Bool.ite wd_cond wd_value Value.undefined) in
  (value, Control.empty, assertion, Bool.fl)

(* Well-defined condition =
 *  IsFloat64(pval) /\ WellDefined(pval)
 * Deoptimization condition =
 *  LostPrecision(pval) 
 *  \/ (hint=CheckForMinusZero /\ pval = -0.0)
 *)
let checked_float64_to_int32 _hint vid pval =
  let value = Value.init vid in
  let wd_cond =
    Bool.ands [ Value.is_defined pval; Value.has_type Type.float64 pval ]
  in

  let value32 = pval |> Value.Float64.to_int32 in

  (* TODO: handing deoptimization *)
  (* let deopt_cond =
       let check_lost_precision =
         Value.eq pval (value32 |> Value.Float64.from_value)
       in
       let check_minus_zero =
         if hint = "dont-check-for-minus-zero" then Bool.tr
         else if hint = "check-for-minus-zero" then
           Value.Float64.is_minus_zero pval
         else
           let reason =
             Format.sprintf "CheckedFloat64ToInt32: invalid hint(%s)" hint
           in
           failwith reason
       in
       Bool.ors [ check_lost_precision; check_minus_zero ]
     in *)
  let wd_value = value32 in
  let assertion = Value.eq value (Bool.ite wd_cond wd_value Value.undefined) in

  (value, Control.empty, assertion, Bool.fl)

(* Well-defined condition =
 *  IsTaggedSigned(pval) /\ WellDefined(pval)
 * Deoptimization condition =
 *  IsNotTaggedSigned(pval)
 * Assertion = 
 *  value = ite well-defined Int32(pval >> 1) UV *)
let checked_tagged_signed_to_int32 vid pval =
  let value = Value.init vid in
  let wd_cond =
    Bool.ands [ Value.is_defined pval; Value.has_type Type.tagged_signed pval ]
  in

  (* TODO: handling deoptimization *)
  (* let deopt_cond = Bool.not (Value.has_type Type.tagged_signed pval) in *)
  let wd_value = Value.TaggedSigned.to_int32 pval in
  let assertion = Value.eq value (Bool.ite wd_cond wd_value Value.undefined) in

  (value, Control.empty, assertion, Bool.fl)
