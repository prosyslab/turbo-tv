open Z3utils
module HeapNumber = Objects.HeapNumber

(* simplified: arithmetic *)
(* well-defined condition:
 * - TaggedSigned(lval) ^ TaggedSigned(rval)
 * - WellDefined(lval) ^ WellDefined(rval)
 * assertion:
 *  value = ite well-defined ((lval+rval) mod 2**64) UB *)
let speculative_safe_integer_add vid lval rval =
  let value = Value.init vid in

  let res = Value.andi (Value.add lval rval) Constants.smi_mask in

  let assertion =
    Bool.ands
      [
        Value.has_type Type.tagged_signed lval;
        Value.has_type Type.tagged_signed rval;
        Value.eq value res;
      ]
  in

  (value, assertion, Bool.fl)

let number_expm1 vid nptr mem =
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
  let res_ptr = HeapNumber.allocate in
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
    |> HeapNumber.from_ieee_bv
  in
  HeapNumber.store res_ptr expm1 wd_cond mem;
  let wd_value = res_ptr in

  let assertion = Value.eq value (Bool.ite wd_cond wd_value Value.undefined) in
  (value, assertion, ub_cond)

(* simplified: memory *)
let allocate_raw vid size =
  let vid = Value.init vid in
  let ptr = Memory.allocate size in
  (ptr, Value.eq vid ptr, Bool.fl)

let store_field ptr pos mt value mem =
  let repr = MachineType.repr mt in

  (* ptr must be pointer type *)
  let ty_check = Value.has_type Type.pointer ptr in

  (* check index out-of-bounds *)
  let can_access = Pointer.can_access_as pos repr ptr in
  let ub_cond = Bool.not (Bool.ands [ ty_check; can_access ]) in
  let store_cond = Bool.not ub_cond in

  mem := Memory.store_as (Pointer.move ptr pos) repr store_cond value !mem;
  (Value.empty, Bool.tr, ub_cond)

(* simplified: type-conversion *)
(* well-defined condition:
 * - int32(pval)
 * - WellDefined(pval)
 * assertion:
 *  value = ite well-defined (tagged(pval)) UB *)
let change_int32_to_tagged vid pval mem =
  let value = Value.init vid in
  let data = Value.data_of pval in

  let wd_cond =
    Bool.ands [ Value.is_defined pval; Value.has_type Type.int32 pval ]
  in

  (* check if pval+pval >= smi max *)
  let is_in_smi_range = Value.is_in_smi_range pval in
  let smi = BitVec.addb data data |> Value.entype Type.tagged_signed in

  let ptr = HeapNumber.allocate in
  let number_value = data |> Float.from_signed_bv |> Float.to_ieee_bv in
  let obj = HeapNumber.from_ieee_bv number_value in
  HeapNumber.store ptr obj is_in_smi_range mem;

  let wd_value = Bool.ite is_in_smi_range smi ptr in
  let assertion = Value.eq value (Bool.ite wd_cond wd_value Value.undefined) in
  (value, assertion, Bool.fl)

(* well-defined condition:
 * - int64(pval) 
 * - WellDefined(lval)
 * assertion:
 *  value = ite well-defined (tagged(pval)) UB *)
let change_int64_to_tagged vid pval mem =
  let value = Value.init vid in
  let data = Value.data_of value in

  let wd_cond =
    Bool.ands [ Value.is_defined pval; Value.has_type Type.int64 pval ]
  in

  (* if pval is in smi range, value = (pval + pval) *)
  let is_in_smi_range = Value.is_in_smi_range pval in
  let smi = BitVec.addb data data |> Value.entype Type.tagged_signed in

  let ptr = HeapNumber.allocate in
  let number_value = data |> Float.from_signed_bv |> Float.to_ieee_bv in
  let obj = HeapNumber.from_ieee_bv number_value in
  HeapNumber.store ptr obj (Bool.not is_in_smi_range) mem;

  let wd_value = Bool.ite is_in_smi_range smi ptr in
  let assertion = Value.eq value (Bool.ite wd_cond wd_value Value.undefined) in
  (value, assertion, Bool.fl)

let checked_tagged_signed_to_int32 vid pval =
  let value = Value.init vid in

  (* TODO: handling deoptimization *)
  (* let deopt = Bool.not (is_tagged_signed pval) in *)
  let result = BitVec.ashri (Value.data_of pval) 1 |> Value.entype Type.int32 in
  let assertion =
    Bool.ands [ Value.has_type Type.tagged_signed pval; Value.eq value result ]
  in

  (value, assertion, Bool.fl)
