module Params = State.Params
open Common
open Simplified
open Machine
open Z3utils

let ctx = Z3utils.ctx

let validator = Solver.init

let rec next program state =
  let pc = State.pc state in
  let rf = State.register_file state in
  let mem = ref (State.memory state) in
  let params = State.params state in
  let vid = !RegisterFile.prefix ^ string_of_int pc in

  let opcode, operands = IR.instr_of pc program in
  let next_pc = match opcode with End -> -1 | _ -> pc + 1 in

  let value, assertion =
    match opcode with
    (* common: constants *)
    | HeapConstant | ExternalConstant ->
        let addr_re = Re.Pcre.regexp "(0x[0-9a-f]+)" in
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
        let conds = RegisterFile.find_all (operands |> Operands.id_of_all) rf in
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
    | End ->
        let return_values =
          RegisterFile.find_all (operands |> Operands.id_of_all) rf
        in
        let value = Value.init vid in
        let assertion =
          Bool.ands
            (List.map
               (fun rv ->
                 Bool.ite
                   (Value.has_type Type.empty rv)
                   Bool.tr (Value.is_equal value rv))
               return_values)
        in
        (value, assertion)
    (* simplified: arithmetic *)
    | SpeculativeSafeIntegerAdd ->
        let lpid = Operands.id_of_nth operands 0 in
        let rpid = Operands.id_of_nth operands 1 in
        let lval = RegisterFile.find lpid rf in
        let rval = RegisterFile.find rpid rf in
        speculative_safe_integer_add vid lval rval
    | NumberExpm1 ->
        let pid = Operands.id_of_nth operands 0 in
        let pval = RegisterFile.find pid rf in
        number_expm1 vid pval
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
        let ptr_id = Operands.id_of_nth operands 0 in
        let ptr = RegisterFile.find ptr_id rf in
        let pos_id = Operands.id_of_nth operands 1 in
        let pos = RegisterFile.find pos_id rf in
        let repr = Operands.const_of_nth operands 2 |> Repr.of_string in
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
    | IfTrue | IfFalse -> Value.is_true value
    | Merge ->
        let size = Composed.size_of value in
        let rec merge_conds res idx value =
          if idx = size then res
          else
            let cond = Composed.select idx value in
            merge_conds (Value.or_ cond res) (idx + 1) value
        in
        merge_conds Value.fl 0 value |> Value.is_true
    | End -> Bool.tr
    | _ -> State.condition state
  in

  let updated_rf = RegisterFile.add vid value rf in
  let updated_asrt =
    Bool.ands
      [
        State.assertion state;
        Bool.ite exec_cond assertion (Value.is_empty value);
      ]
  in

  let next_state =
    State.update next_pc updated_rf exec_cond updated_asrt state
  in

  if State.is_final next_state then
    (BitVec.init ~len:Value.len vid, State.assertion next_state)
  else next program next_state

(* execute the program and retrieve a final state *)
let execute program nparams stage =
  (* symbols for parameters *)
  let init_state = State.init nparams stage in
  next program init_state

let run nparams before after =
  let retvar_A, assertion_A = execute before nparams "before" in
  let retvar_B, assertion_B = execute after nparams "after" in

  let assertion =
    Bool.ands [ assertion_A; assertion_B; Bool.neq retvar_A retvar_B ]
  in

  let status = Solver.check validator assertion in

  match status with
  | SATISFIABLE ->
      let model = Option.get (Solver.get_model validator) in
      let model_str = model |> Model.to_str in

      Printf.printf "X -> \n";
      Printf.printf "Assertion: \n%s\n" (assertion |> str_of_simplified);
      Printf.printf "Model: \n%s" model_str
  | UNSATISFIABLE -> Printf.printf "O\n"
  | _ -> failwith "unknown"
