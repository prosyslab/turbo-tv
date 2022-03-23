open Z3utils
open Value
module Composed = Value.Composed
module Repr = MachineType.Repr

type id = string
type t = BitVec.t

(* common: constants *)
let int32_constant vid c =
  let value = Value.init vid in
  let cval = c |> Value.from_string |> Value.cast Type.int32 in
  let assertion = Bool.ands [ Value.is_equal value cval ] in
  (value, assertion)

let int64_constant vid c =
  let value = Value.init vid in
  let cval = c |> Value.from_string |> Value.cast Type.int64 in
  let assertion = Bool.ands [ Value.is_equal value cval ] in
  (value, assertion)

let external_constant vid c =
  let value = Value.init vid in
  let cval = c |> Value.from_string |> Value.cast Type.pointer in
  let assertion = Bool.ands [ Value.is_equal value cval ] in
  (value, assertion)

let heap_constant = external_constant

let number_constant vid n =
  let value = Value.init vid in
  let cval = Value.from_string n in

  let can_be_smi = Value.can_be_smi cval in
  let tr =
    (* shift-left once  *)
    let smi_value = Value.shli value 1 |> Value.cast Type.tagged_signed in
    Value.is_equal value smi_value
  in
  let fl = Value.is_equal value (cval |> Value.cast Type.any_tagged) in

  let assertion = Bool.ite can_be_smi tr fl in
  (value, assertion)

(* common: control *)
(* retrieve the value at [idx] from [incoming] *)
(* incoming: | --- idx[0] ---| --- idx[1] --- | --- ... --- | *)
let projection vid idx incoming =
  (* currently, idx of projection is assumebed to be less than 2 *)
  let value = Value.init vid in
  let undefined = idx >= Composed.size_of incoming || idx >= 2 in
  let res =
    if not undefined then Composed.select idx incoming else Value.undefined
  in
  let assertion = Value.is_equal value res in
  (value, assertion)

(* | --- True Condition --- | --- False Condition --- | *)
(* True condition: precond ^ cond *)
(* False condition: precond ^ not cond *)
let branch vid cond precond =
  let value = Composed.init vid 2 in

  let conds_are_bool =
    Bool.ands
      [ Value.has_type Type.bool cond; Value.has_type Type.bool precond ]
  in
  let conds_are_defined =
    Bool.ands [ Value.is_defined cond; Value.is_defined precond ]
  in

  let is_well_defined = Bool.ands [ conds_are_bool; conds_are_defined ] in
  let defined =
    let true_cond = Value.and_ precond cond |> Value.cast Type.bool in
    let false_cond =
      Value.and_ precond (Value.not_ cond) |> Value.cast Type.bool
    in
    Value.is_equal value (BitVec.concat true_cond false_cond)
  in
  let undefined =
    let ubool = Value.undefined |> Value.cast Type.bool in
    Value.is_equal value (BitVec.concat ubool ubool)
  in
  let cond = BitVec.concat if_true if_false in

  let assertion = Bool.ite is_well_defined defined undefined in
  (value, assertion)

(* collect all return values *)
let end_ vid values =
  let value = Value.init vid in
  let assertion = BitVec.eqb value (Bool.ands values) in
  (value, assertion)

let if_false vid cond =
  let value = Value.init vid in

  let false_cond = cond |> Composed.second_of in
  let cond_is_defined = Value.is_defined false_cond in
  let cond_is_bool = false_cond |> Value.has_type Type.bool in

  let is_well_defined = Bool.ands [ cond_is_defined; cond_is_bool ] in
  let defined = Value.is_equal value false_cond in
  let undefined =
    Value.is_equal value (Value.undefined |> Value.cast Type.bool)
  in

  let assertion = Bool.ite is_well_defined defined undefined in
  (value, assertion)

let if_true vid cond =
  let value = Value.init vid in

  let true_cond = cond |> Composed.first_of in
  let is_cond_defined = Value.is_defined true_cond in
  let is_cond_bool = cond |> Value.has_type Type.bool in

  let is_well_defined = Bool.ands [ is_cond_defined; is_cond_bool ] in
  let defined = Value.is_equal value (cond |> Composed.first_of) in
  let undefined =
    Value.is_equal value (Value.undefined |> Value.cast Type.bool)
  in

  let assertion = Bool.ite is_well_defined defined undefined in
  (value, assertion)

(* merge every incoming execution condition *)
let merge vid conds =
  let value = Value.init vid in
  let assertion =
    BitVec.eqb value
      (entype Type.bool
         (List.fold_left
            (fun asrt cond -> BitVec.orb asrt (data_of cond))
            (BitVecVal.tr ()) conds))
  in
  (value, assertion)

(* common: procedure *)
let parameter vid param =
  let value = Value.init vid in
  let assertion = BitVec.eqb value (param |> cast Type.tagged_signed) in
  (value, assertion)

let return vid return_value =
  let value = Value.init vid in
  let assertion = BitVec.eqb value return_value in
  (value, assertion)

(* simplified: arithmetic *)
let speculative_safe_integer_add vid lval rval =
  let value = Value.init vid in

  let res =
    Value.mask (Value.add lval rval) (Value.from_int Type.smi_mask)
    |> cast Type.tagged_signed
  in

  let assertion =
    Bool.ands
      [
        Value.has_type Type.tagged_signed lval;
        Value.has_type Type.tagged_signed rval;
        is_equal value res;
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
  let data = data_of pval in

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
        is_equal value (pval |> cast Type.tagged_signed);
      ]
  in
  (value, assertion)

let checked_tagged_signed_to_int32 vid pval =
  let value = Value.init vid in

  (* TODO: handling deoptimization *)
  (* let deopt = Bool.not (is_tagged_signed pval) in *)
  let result = BitVec.ashri (data_of pval) 1 |> Value.entype Type.int32 in
  let assertion =
    Bool.ands
      [ Value.has_type Type.tagged_signed pval; Value.is_equal value result ]
  in

  (value, assertion)

(* machine: arithmetic *)
(* value = (lval + rval) mod 2^32 *)
let int32add vid lval rval =
  let value = Value.init vid in
  let res =
    Value.mask (Value.add lval rval) (Type.smi_mask |> Value.from_int)
    |> cast Type.int32
  in

  let assertion =
    Bool.ands
      [
        Value.has_type Type.int32 lval;
        Value.has_type Type.int32 rval;
        is_equal value res;
      ]
  in

  (value, assertion)

let int32add_with_overflow vid lval rval =
  let value = Composed.init vid 2 in

  let ldata = data_of lval in
  let rdata = data_of rval in
  let res =
    BitVec.andi (BitVec.addb ldata rdata) Type.smi_mask |> entype Type.int32
  in
  let ovf =
    Bool.ite
      (BitVec.ulti (BitVec.addb ldata rdata) Type.smi_max)
      (BitVecVal.tr ()) (BitVecVal.fl ())
    |> entype Type.bool
  in

  let assertion =
    Bool.ands
      [
        Value.has_type Type.int32 lval;
        Value.has_type Type.int32 rval;
        is_equal (Composed.second_of value) ovf;
        is_equal (Composed.first_of value) res;
      ]
  in

  (value, assertion)

(* var = (lval + rval) mod 2^64 *)
let int64add vid lval rval =
  let value = Value.init vid in

  let ldata = data_of lval in
  let rdata = data_of rval in
  let res = BitVec.addb ldata rdata |> entype Type.int64 in

  let assertion =
    Bool.ands
      [
        Value.has_type Type.int64 lval;
        Value.has_type Type.int64 rval;
        is_equal value res;
      ]
  in

  (value, assertion)

let int64sub vid lval rval =
  let value = Value.init vid in

  let ldata = data_of lval in
  let rdata = data_of rval in
  let res = BitVec.subb ldata rdata |> entype Type.int64 in

  let assertion =
    Bool.ands
      [
        Value.has_type Type.int64 lval;
        Value.has_type Type.int64 rval;
        is_equal value res;
      ]
  in

  (value, assertion)

let word32sar vid hint lval rval =
  let value = Value.init vid in

  let is_shift_out_zero =
    if String.equal hint "ShfitOutZero" then Bool.tr else Bool.fl
  in

  let ldata = data_of lval in
  let rdata = data_of rval in
  let lval_ty = ty_of lval in

  let res =
    BitVec.andi (BitVec.ashrb ldata rdata) Type.smi_mask |> entype lval_ty
  in

  let assertion =
    Bool.ands
      [
        Value.has_repr Repr.Word32 lval;
        Value.has_repr Repr.Word32 rval;
        is_equal value res;
        Bool.ors
          [ is_shift_out_zero; (* TODO: undef *) is_weak_equal res Value.empty ];
      ]
  in
  (value, assertion)

(* machine: comparison *)
let word32and vid lval rval =
  let value = Value.init vid in
  let ldata = data_of lval in
  let rdata = data_of rval in
  let ty = ty_of lval in
  let res = BitVec.andb ldata rdata |> entype ty in
  let assertion =
    Bool.ands
      [
        Value.has_repr Repr.Word32 lval;
        Value.has_repr Repr.Word32 rval;
        is_equal value res;
      ]
  in
  (value, assertion)

let word32equal vid lval rval =
  let value = Value.init vid in
  let ldata = data_of lval in
  let rdata = data_of rval in
  let res =
    Bool.ite (BitVec.eqb ldata rdata) (BitVecVal.tr ()) (BitVecVal.fl ())
    |> entype Type.bool
  in

  let assertion =
    Bool.ands
      [
        Value.has_repr Repr.Word32 lval;
        Value.has_repr Repr.Word32 rval;
        is_equal value res;
      ]
  in

  (value, assertion)

let uint64less_than vid lval rval =
  let value = Value.init vid in

  let ldata = data_of lval in
  let rdata = data_of rval in
  let res =
    Bool.ite (BitVec.ultb ldata rdata) (BitVecVal.tr ()) (BitVecVal.fl ())
    |> cast Type.bool
  in

  let assertion =
    Bool.ands
      [
        Value.has_type Type.uint64 lval;
        Value.has_type Type.uint64 rval;
        is_equal value res;
      ]
  in

  (value, assertion)

(* machine: memory *)
let store ptr pos repr value mem =
  (* ptr must be pointer type *)
  let ty_check = Value.has_type Type.pointer ptr in

  (* check index out-of-bounds *)
  let struct_size = Pointer.size_of ptr in
  let store_size = repr |> Repr.size_of in
  let oob_check =
    Bool.ands
      [
        BitVec.sgei pos 0; BitVec.uleb (BitVec.addi pos store_size) struct_size;
      ]
  in

  let condition = Bool.ands [ ty_check; oob_check ] in
  mem := Memory.store (Pointer.move ptr pos) store_size condition value !mem;

  (Value.empty, Bool.tr)

let load vid ptr pos repr mem =
  (* ptr must be pointer type *)
  let ty_check = Value.has_type Type.pointer ptr in

  (* check index out-of-bounds *)
  let can_read = Pointer.can_access_as pos repr ptr in

  let value = Value.init vid in
  let loaded = Memory.load_as (Pointer.move ptr pos) repr mem in

  let assertion =
    Bool.ands [ ty_check; can_read; Value.is_weak_equal value loaded ]
  in
  (value, assertion)

(* machine: type-conversion *)
let bitcast_tagged_to_word vid pval =
  let value = Value.init vid in
  let assertion =
    Bool.ands
      [
        Value.has_type Type.any_tagged pval;
        is_equal value (pval |> cast Type.uint64);
      ]
  in

  (value, assertion)

let bitcast_word32_to_word64 vid pval =
  let value = Value.init vid in
  let assertion =
    Bool.ands
      [
        Value.has_repr Repr.Word32 pval;
        is_equal value (pval |> cast Type.uint64);
      ]
  in

  (value, assertion)

let bitcast_word_to_tagged vid pval =
  let value = Value.init vid in
  let assertion =
    Bool.ands
      [
        Value.has_repr Word32 pval; is_equal value (pval |> cast Type.any_tagged);
      ]
  in
  (value, assertion)

let truncate_int64_to_int32 vid pval =
  let value = Value.init vid in
  let assertion =
    Bool.ands
      [
        Value.has_type Type.int64 pval; is_equal value (pval |> cast Type.int32);
      ]
  in
  (value, assertion)

(* apply semantics to create SMT query *)
let apply program state =
  let pc = State.pc state in
  let rf = State.register_file state in
  let mem = ref (State.memory state) in
  let params = State.params state in
  let vid = !RegisterFile.prefix ^ string_of_int pc in

  let opcode, operands = IR.instr_of pc program in
  let next_pc = match opcode with Return -> -1 | _ -> pc + 1 in

  let value, assertion =
    match opcode with
    (* common: constants *)
    | HeapConstant | ExternalConstant ->
        let addr_re = Re.Pcre.regexp "(0x[0-9a-f]*)" in
        let operand = Operands.const_of_nth operands 0 in
        Re.Group.get (Re.exec addr_re operand) 1 |> heap_constant vid
    | Int32Constant -> Operands.const_of_nth operands 0 |> int32_constant vid
    | Int64Constant -> Operands.const_of_nth operands 0 |> int64_constant vid
    | NumberConstant -> Operands.const_of_nth operands 0 |> number_constant vid
    (* common: control *)
    | Projection ->
        let idx = Operands.const_of_nth operands 0 |> int_of_string in
        let id = Operands.id_of_nth operands 1 in
        let incoming = RegisterFile.find id rf in
        projection vid idx incoming
    | Branch ->
        let cond_id = Operands.id_of_nth operands 0 in
        let prev_id = Operands.id_of_nth operands 1 in
        let cond_value = RegisterFile.find cond_id rf in
        let precond_value = RegisterFile.find prev_id rf in
        branch vid cond_value precond_value
    | IfFalse ->
        let nid = Operands.id_of_nth operands 0 in
        let cond_value = RegisterFile.find nid rf in
        if_false vid cond_value
    | IfTrue ->
        let nid = Operands.id_of_nth operands 0 in
        let cond_value = RegisterFile.find nid rf in
        if_true vid cond_value
    | Start -> (Value.empty, Bool.tr)
    | Merge ->
        let nids =
          List.map (fun operand -> operand |> Operands.Operand.id) operands
        in
        let conds = List.map (fun nid -> RegisterFile.find nid rf) nids in
        merge vid conds
    (* common: procedure *)
    | Parameter ->
        let pidx = Operands.const_of_nth operands 0 |> int_of_string in
        if 0 < pidx && pidx <= List.length params then
          let param = List.nth params (pidx - 1) in
          parameter vid param
        else (Value.empty, Bool.tr)
    | Call -> (Value.empty, Bool.tr)
    | Return ->
        let nid = Operands.id_of_nth operands 0 in
        let return_value = RegisterFile.find nid rf in
        return vid return_value
    | End -> (Value.empty, Bool.tr)
    (* simplified: arithmetic *)
    | SpeculativeSafeIntegerAdd ->
        let lpid = Operands.id_of_nth operands 0 in
        let rpid = Operands.id_of_nth operands 1 in
        let lval = RegisterFile.find lpid rf in
        let rval = RegisterFile.find rpid rf in
        speculative_safe_integer_add vid lval rval
    (* simplified: memory *)
    | AllocateRaw ->
        let size_id = Operands.id_of_nth operands 0 in
        let size_value = RegisterFile.find size_id rf in
        allocate_raw vid size_value
    | StoreField ->
        let ptr_id = Operands.id_of_nth operands 0 in
        let ptr = RegisterFile.find ptr_id rf in
        let pos =
          Operands.const_of_nth operands 1 |> BitVecVal.of_str ~len:Value.len
        in
        let machine_type =
          Operands.const_of_nth operands 2 |> MachineType.of_rs_string
        in
        let value_id = Operands.id_of_nth operands 3 in
        let value = RegisterFile.find value_id rf in
        store_field ptr pos machine_type value mem
    (* simplified: type-conversion *)
    | ChangeInt32ToTagged ->
        let pid = Operands.id_of_nth operands 0 in
        let pval = RegisterFile.find pid rf in
        change_int32_to_tagged vid pval mem
    | ChangeInt32ToFloat64 ->
        let pid = Operands.id_of_nth operands 0 in
        let pval = RegisterFile.find pid rf in
        change_int32_to_float64 vid pval
    | CheckedTaggedSignedToInt32 ->
        let pid = Operands.id_of_nth operands 0 in
        let pval = RegisterFile.find pid rf in
        checked_tagged_signed_to_int32 vid pval
    (* machine: arithmetic *)
    | Int32Add ->
        let lpid = Operands.id_of_nth operands 0 in
        let rpid = Operands.id_of_nth operands 1 in
        let lval = RegisterFile.find lpid rf in
        let rval = RegisterFile.find rpid rf in
        int32add vid lval rval
    | Int32AddWithOverflow ->
        let lpid = Operands.id_of_nth operands 0 in
        let rpid = Operands.id_of_nth operands 1 in
        let lval = RegisterFile.find lpid rf in
        let rval = RegisterFile.find rpid rf in
        int32add_with_overflow vid lval rval
    | Int64Add ->
        let lpid = Operands.id_of_nth operands 0 in
        let rpid = Operands.id_of_nth operands 1 in
        let lval = RegisterFile.find lpid rf in
        let rval = RegisterFile.find rpid rf in
        int64add vid lval rval
    | Int64Sub ->
        let lpid = Operands.id_of_nth operands 0 in
        let rpid = Operands.id_of_nth operands 1 in
        let lval = RegisterFile.find lpid rf in
        let rval = RegisterFile.find rpid rf in
        int64sub vid lval rval
    | Word32Sar ->
        let hint = Operands.const_of_nth operands 0 in
        let lpid = Operands.id_of_nth operands 1 in
        let rpid = Operands.id_of_nth operands 2 in
        let lval = RegisterFile.find lpid rf in
        let rval = RegisterFile.find rpid rf in
        word32sar vid hint lval rval
    (* machine: comparison *)
    | StackPointerGreaterThan -> (Value.empty, Bool.tr)
    | Word32And ->
        let lpid = Operands.id_of_nth operands 0 in
        let rpid = Operands.id_of_nth operands 1 in
        let lval = RegisterFile.find lpid rf in
        let rval = RegisterFile.find rpid rf in
        word32and vid lval rval
    | Word32Equal ->
        let lpid = Operands.id_of_nth operands 0 in
        let rpid = Operands.id_of_nth operands 1 in
        let lval = RegisterFile.find lpid rf in
        let rval = RegisterFile.find rpid rf in
        word32equal vid lval rval
    | Uint64LessThan ->
        let lpid = Operands.id_of_nth operands 0 in
        let rpid = Operands.id_of_nth operands 1 in
        let lval = RegisterFile.find lpid rf in
        let rval = RegisterFile.find rpid rf in
        uint64less_than vid lval rval
    (* machine: memory *)
    | Store ->
        let ptr_id = Operands.id_of_nth operands 0 in
        let ptr = RegisterFile.find ptr_id rf in

        let pos_id = Operands.id_of_nth operands 1 in
        let pos = RegisterFile.find pos_id rf in

        let repr = Operands.const_of_nth operands 2 |> Repr.of_string in

        let value_id = Operands.id_of_nth operands 3 in
        let value = RegisterFile.find value_id rf in
        store ptr pos repr value mem
    | Load ->
        let ptr_id = Operands.id_of_nth operands 1 in
        let ptr = RegisterFile.find ptr_id rf in
        let pos_id = Operands.id_of_nth operands 2 in
        let pos = RegisterFile.find pos_id rf in
        let repr = Operands.const_of_nth operands 0 |> Repr.of_string in
        load vid ptr pos repr !mem
    (* machine: bitcast *)
    | BitcastTaggedToWord ->
        let pid = Operands.id_of_nth operands 0 in
        let pval = RegisterFile.find pid rf in
        bitcast_tagged_to_word vid pval
    | BitcastWord32ToWord64 ->
        let pid = Operands.id_of_nth operands 0 in
        let pval = RegisterFile.find pid rf in
        bitcast_word32_to_word64 vid pval
    | BitcastWordToTagged ->
        let pid = Operands.id_of_nth operands 0 in
        let pval = RegisterFile.find pid rf in
        bitcast_word_to_tagged vid pval
    | TruncateInt64ToInt32 ->
        let pid = Operands.id_of_nth operands 0 in
        let pval = RegisterFile.find pid rf in
        truncate_int64_to_int32 vid pval
    | Empty -> (Value.empty, Bool.tr)
    | _ -> (Value.empty, Bool.tr)
  in

  let exec_cond =
    match opcode with
    | IfTrue | IfFalse | Merge -> BitVec.is_true value
    | _ -> State.condition state
  in

  let updated_rf = RegisterFile.add vid value rf in
  let updated_asrt =
    Bool.ands [ State.assertion state; Bool.ite exec_cond assertion Bool.fl ]
  in
  let next_state =
    State.update next_pc updated_rf exec_cond updated_asrt state
  in

  if State.is_final next_state then
    { next_state with retvar = Option.some (BitVec.init ~len:Value.len vid) }
  else next_state
