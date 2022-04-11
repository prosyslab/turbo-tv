open Z3utils
module Composed = Value.Composed
module Repr = MachineType.Repr

(* machine: arithmetic *)
(* value = (lval + rval) mod 2^32 *)
let int32add vid lval rval =
  let value = Value.init vid in
  let res =
    Value.mask (Value.add lval rval) (Type.smi_mask |> Value.from_int)
    |> Value.cast Type.int32
  in

  let assertion =
    Bool.ands
      [
        Value.has_type Type.int32 lval;
        Value.has_type Type.int32 rval;
        Value.is_equal value res;
      ]
  in

  (value, assertion)

let int32add_with_overflow vid lval rval =
  let value = Composed.init vid 2 in

  let ldata = Value.data_of lval in
  let rdata = Value.data_of rval in
  let res =
    BitVec.andi (BitVec.addb ldata rdata) Type.smi_mask
    |> Value.entype Type.int32
  in
  let ovf =
    Bool.ite
      (BitVec.ulti (BitVec.addb ldata rdata) Type.smi_max)
      (BitVecVal.tr ()) (BitVecVal.fl ())
    |> Value.entype Type.bool
  in

  let assertion =
    Bool.ands
      [
        Value.has_type Type.int32 lval;
        Value.has_type Type.int32 rval;
        Value.is_equal (Composed.second_of value) ovf;
        Value.is_equal (Composed.first_of value) res;
      ]
  in

  (value, assertion)

(* var = (lval + rval) mod 2^64 *)
let int64add vid lval rval =
  let value = Value.init vid in

  let ldata = Value.data_of lval in
  let rdata = Value.data_of rval in
  let res = BitVec.addb ldata rdata |> Value.entype Type.int64 in

  let assertion =
    Bool.ands
      [
        Value.has_type Type.int64 lval;
        Value.has_type Type.int64 rval;
        Value.is_equal value res;
      ]
  in

  (value, assertion)

let int64sub vid lval rval =
  let value = Value.init vid in

  let ldata = Value.data_of lval in
  let rdata = Value.data_of rval in
  let res = BitVec.subb ldata rdata |> Value.entype Type.int64 in

  let assertion =
    Bool.ands
      [
        Value.has_type Type.int64 lval;
        Value.has_type Type.int64 rval;
        Value.is_equal value res;
      ]
  in

  (value, assertion)

let word32sar vid hint lval rval =
  let value = Value.init vid in

  let is_shift_out_zero =
    if String.equal hint "ShfitOutZero" then Bool.tr else Bool.fl
  in

  let ldata = Value.data_of lval in
  let rdata = Value.data_of rval in
  let lval_ty = Value.ty_of lval in

  let res =
    BitVec.andi (BitVec.ashrb ldata rdata) Type.smi_mask |> Value.entype lval_ty
  in

  let assertion =
    Bool.ands
      [
        Value.has_repr Repr.Word32 lval;
        Value.has_repr Repr.Word32 rval;
        Value.is_equal value res;
        Bool.ors
          [
            is_shift_out_zero;
            (* TODO: undef *)
            Value.is_weak_equal res Value.empty;
          ];
      ]
  in
  (value, assertion)

(* machine: comparison *)
let word32and vid lval rval =
  let value = Value.init vid in
  let ldata = Value.data_of lval in
  let rdata = Value.data_of rval in
  let ty = Value.ty_of lval in
  let res = BitVec.andb ldata rdata |> Value.entype ty in
  let assertion =
    Bool.ands
      [
        Value.has_repr Repr.Word32 lval;
        Value.has_repr Repr.Word32 rval;
        Value.is_equal value res;
      ]
  in
  (value, assertion)

let word32equal vid lval rval =
  let value = Value.init vid in
  let ldata = Value.data_of lval in
  let rdata = Value.data_of rval in
  let res =
    Bool.ite (BitVec.eqb ldata rdata) (BitVecVal.tr ()) (BitVecVal.fl ())
    |> Value.entype Type.bool
  in

  let assertion =
    Bool.ands
      [
        Value.has_repr Repr.Word32 lval;
        Value.has_repr Repr.Word32 rval;
        Value.is_equal value res;
      ]
  in

  (value, assertion)

let uint64less_than vid lval rval =
  let value = Value.init vid in
  let res = Bool.ite (Value.ult lval rval) Value.tr Value.fl in

  let assertion =
    Bool.ands
      [
        Value.has_type Type.uint64 lval;
        Value.has_type Type.uint64 rval;
        Value.is_equal value res;
      ]
  in

  (value, assertion)

(* machine: memory *)
(* wip: handling undef *)
let store ptr pos repr value mem =
  (* ptr must be pointer type & well-defined *)
  let ptr_is_pointer = Value.has_type Type.pointer ptr in
  let ptr_is_defined = Value.is_defined ptr in

  (* check index out-of-bounds *)
  let can_write = Pointer.can_access_as pos repr ptr in
  let condition = Bool.ands [ ptr_is_pointer; ptr_is_defined; can_write ] in

  let store_size = repr |> Repr.size_of in
  mem := Memory.store ptr store_size condition value !mem;
  (Value.empty, Bool.tr)

(* wip: handling undef *)
let load vid ptr pos repr mem =
  (* ptr must be pointer type & well-defined *)
  let ptr_is_pointer = Value.has_type Type.pointer ptr in
  let ptr_is_defined = Value.is_defined ptr in

  (* check index out-of-bounds *)
  let can_write = Pointer.can_access_as pos repr ptr in
  let condition = Bool.ands [ ptr_is_pointer; ptr_is_defined; can_write ] in

  let value = Value.init vid in
  let loaded = Memory.load_as (Pointer.move ptr pos) repr mem in

  let assertion =
    Bool.ite condition
      (Value.is_weak_equal value loaded)
      (Value.is_equal value Value.undefined)
  in
  (value, assertion)

(* machine: type-conversion *)
let bitcast_tagged_to_word vid pval =
  let value = Value.init vid in
  let assertion =
    Bool.ands
      [
        Value.has_type Type.any_tagged pval;
        Value.is_equal value (pval |> Value.cast Type.uint64);
      ]
  in

  (value, assertion)

let bitcast_word32_to_word64 vid pval =
  let value = Value.init vid in
  let assertion =
    Bool.ands
      [
        Value.has_repr Repr.Word32 pval;
        Value.is_equal value (pval |> Value.cast Type.uint64);
      ]
  in

  (value, assertion)

let bitcast_word_to_tagged vid pval =
  let value = Value.init vid in
  let assertion =
    Bool.ands
      [
        Value.has_repr Word32 pval;
        Value.is_equal value (pval |> Value.cast Type.any_tagged);
      ]
  in
  (value, assertion)

let truncate_int64_to_int32 vid pval =
  let value = Value.init vid in
  let assertion =
    Bool.ands
      [
        Value.has_type Type.int64 pval;
        Value.is_equal value (pval |> Value.cast Type.int32);
      ]
  in
  (value, assertion)
