open Z3utils

(* simplified: arithmetic *)
let speculative_safe_integer_add vid lval rval =
  let value = Value.init vid in

  let res =
    Value.mask (Value.add lval rval) (Value.from_int Type.smi_mask)
    |> Value.cast Type.tagged_signed
  in

  let assertion =
    Bool.ands
      [
        Value.has_type Type.tagged_signed lval;
        Value.has_type Type.tagged_signed rval;
        Value.is_equal value res;
      ]
  in

  (value, assertion)

(* simplified: memory *)
let allocate_raw vid size =
  let ptr, assertion = Memory.allocate vid size in
  (ptr, assertion)

let store_field ptr pos mt value mem =
  let repr = MachineType.repr mt in

  (* ptr must be pointer type *)
  let ty_check = Value.has_type Type.pointer ptr in

  (* check index out-of-bounds *)
  let can_access = Pointer.can_access_as pos repr ptr in
  let condition = Bool.ands [ ty_check; can_access ] in

  mem := Memory.store_as (Pointer.move ptr pos) repr condition value !mem;
  (Value.empty, Bool.tr)

(* simplified: type-conversion *)
let change_int32_to_tagged vid pval mem =
  let value = Value.init vid in
  let data = Value.data_of pval in

  let tagged = BitVec.addb data data in

  (* check if pval+pval >= smi max *)
  let ovf_check = BitVec.ugei tagged Type.smi_max in

  let size = Value.from_int 12 in
  let ptr, assertion = Memory.allocate vid size in
  (* TODO: Define map constants *)
  let heap_number_map = BitVecVal.of_int ~len:32 1234 in
  let would_be_stored = BitVec.concat heap_number_map data in

  mem := Memory.store ptr 12 ovf_check would_be_stored !mem;

  let if_ovf = Bool.ands [ Value.is_equal value ptr; assertion ] in
  let if_not_ovf =
    Value.is_equal value (Value.entype Type.tagged_signed tagged)
  in

  let assertion = Bool.ite ovf_check if_ovf if_not_ovf in
  (value, assertion)

let change_int32_to_float64 vid pval =
  let value = Value.init vid in
  let assertion =
    Bool.ands
      [
        Value.has_type Type.int32 pval;
        Value.is_equal value (pval |> Value.cast Type.tagged_signed);
      ]
  in
  (value, assertion)

let checked_tagged_signed_to_int32 vid pval =
  let value = Value.init vid in

  (* TODO: handling deoptimization *)
  (* let deopt = Bool.not (is_tagged_signed pval) in *)
  let result = BitVec.ashri (Value.data_of pval) 1 |> Value.entype Type.int32 in
  let assertion =
    Bool.ands
      [ Value.has_type Type.tagged_signed pval; Value.is_equal value result ]
  in

  (value, assertion)
