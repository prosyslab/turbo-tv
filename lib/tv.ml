module Params = State.Params
module ControlFile = Control.ControlFile
open Common
open Simplified
open Machine
open Z3utils

let ctx = Z3utils.ctx

let validator = Solver.init (Some "QF_AUFBV")

module Id_set = Set.Make (Int)

let tag base_is_tagged =
  match base_is_tagged with
  | "tagged base" -> 1
  | "untagged base" -> 0
  | _ -> failwith (Printf.sprintf "invalid input: %s" base_is_tagged)

let rec next program state cfg =
  let pc = State.pc state in
  let cf = State.control_file state in
  let rf = State.register_file state in
  let mem = ref (State.memory state) in
  let params = State.params state in
  let vid = !RegisterFile.prefix ^ string_of_int pc in
  let cid = !ControlFile.prefix ^ string_of_int pc in

  let ty, opcode, operands = IR.instr_of pc program in
  let next_pc = match opcode with End -> -1 | _ -> pc + 1 in
  let value, control, assertion, ub =
    match opcode with
    (* common: constants *)
    | Float64Constant ->
        let c =
          Operands.const_of_nth operands 0
          |> Value.from_f64string |> Value.cast Type.float64
        in
        float64_constant vid c
    | HeapConstant | ExternalConstant ->
        let addr_re = Re.Pcre.regexp "(0x[0-9a-f]+)" in
        let operand = Operands.const_of_nth operands 0 in
        let c =
          Re.Group.get (Re.exec addr_re operand) 1 |> Value.from_istring
        in
        heap_constant vid c
    | Int32Constant ->
        let c = Operands.const_of_nth operands 0 |> Value.from_istring in
        int32_constant vid c
    | Int64Constant ->
        let c = Operands.const_of_nth operands 0 |> Value.from_istring in
        int64_constant vid c
    | NumberConstant ->
        let c_str = Operands.const_of_nth operands 0 in
        number_constant vid c_str mem
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
        let precond_token = ControlFile.find prev_id cf in
        branch cid cond_value precond_token
    | IfFalse ->
        let nid = Operands.id_of_nth operands 0 in
        let cond_token = ControlFile.find nid cf in
        if_false cid cond_token
    | IfTrue ->
        let nid = Operands.id_of_nth operands 0 in
        let cond_token = ControlFile.find nid cf in
        if_true cid cond_token
    | Phi ->
        let rev = operands |> List.rev in
        let cond_id = Operands.id_of_nth rev 0 in
        let cond_tokens =
          IR.instr_of (cond_id |> int_of_string) program
          |> fun (_, _, conds_id) ->
          ControlFile.find_all (conds_id |> Operands.id_of_all) cf
        in
        let repr = Operands.const_of_nth rev 1 |> MachineType.Repr.of_string in
        let incoming_values =
          RegisterFile.find_all
            (rev |> List.tl |> List.tl |> List.rev |> Operands.id_of_all)
            rf
        in
        phi vid incoming_values repr cond_tokens
    | Start -> start cid
    | Merge ->
        let conds = ControlFile.find_all (operands |> Operands.id_of_all) cf in
        merge cid conds
    (* common: procedure *)
    | Parameter ->
        let pidx = Operands.const_of_nth operands 0 |> int_of_string in
        if 0 < pidx && pidx <= List.length params then
          let param = List.nth params (pidx - 1) in
          parameter vid param
        else (Value.empty, Control.empty, Bool.tr, Bool.fl)
    | Call -> (Value.tr, Control.empty, Bool.tr, Bool.fl)
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
                   Bool.tr (Value.eq value rv))
               return_values)
        in
        (value, Control.empty, assertion, Bool.fl)
    (* simplified: arithmetic *)
    | NumberAdd ->
        let lpid = Operands.id_of_nth operands 0 in
        let rpid = Operands.id_of_nth operands 1 in
        let lval = RegisterFile.find lpid rf in
        let rval = RegisterFile.find rpid rf in
        number_add vid lval rval
    | SpeculativeNumberBitwiseXor ->
        let lpid = Operands.id_of_nth operands 0 in
        let rpid = Operands.id_of_nth operands 1 in
        let lval = RegisterFile.find lpid rf in
        let rval = RegisterFile.find rpid rf in
        speculative_number_bitwise_xor vid lval rval
    | SpeculativeSafeIntegerAdd ->
        let lpid = Operands.id_of_nth operands 0 in
        let rpid = Operands.id_of_nth operands 1 in
        let lval = RegisterFile.find lpid rf in
        let rval = RegisterFile.find rpid rf in
        speculative_safe_integer_add vid lval rval mem
    | SpeculativeSafeIntegerSubtract ->
        let lpid = Operands.id_of_nth operands 0 in
        let rpid = Operands.id_of_nth operands 1 in
        let lval = RegisterFile.find lpid rf in
        let rval = RegisterFile.find rpid rf in
        speculative_safe_integer_subtract vid lval rval mem
    | NumberExpm1 ->
        let pid = Operands.id_of_nth operands 0 in
        let pval = RegisterFile.find pid rf in
        number_expm1 vid pval mem
    (* simplified: comparison *)
    | BooleanNot ->
        let pid = Operands.id_of_nth operands 0 in
        let pval = RegisterFile.find pid rf in
        boolean_not vid pval
    | ReferenceEqual ->
        let lpid = Operands.id_of_nth operands 0 in
        let rpid = Operands.id_of_nth operands 1 in
        let lval = RegisterFile.find lpid rf in
        let rval = RegisterFile.find rpid rf in
        word32_equal vid lval rval
    (* simplified: memory *)
    | AllocateRaw ->
        let size_id = Operands.id_of_nth operands 0 in
        let size_value = RegisterFile.find size_id rf in
        let ct_id = Operands.id_of_nth operands 1 in
        let ct = ControlFile.find ct_id cf in
        allocate_raw vid cid size_value ct
    | LoadElement ->
        let base_is_tagged = Operands.const_of_nth operands 0 in
        let tag_value = tag base_is_tagged in
        let header_size = Operands.const_of_nth operands 1 |> int_of_string in
        let machine_type = Operands.const_of_nth operands 2 in
        let repr = MachineType.Repr.of_rs_string machine_type in
        let bid_id = Operands.id_of_nth operands 3 in
        let bid = RegisterFile.find bid_id rf in
        let ind_id = Operands.id_of_nth operands 4 in
        let ind = RegisterFile.find ind_id rf in
        load_element vid tag_value header_size repr bid ind !mem
    | StoreField ->
        let ptr_id = Operands.id_of_nth operands 0 in
        let ptr = RegisterFile.find ptr_id rf in
        let pos =
          Operands.const_of_nth operands 1
          |> BitVecVal.from_istring ~len:Value.len
        in
        let machine_type =
          Operands.const_of_nth operands 2 |> MachineType.of_rs_string
        in
        let value_id = Operands.id_of_nth operands 3 in
        let value = RegisterFile.find value_id rf in
        store_field ptr pos machine_type value mem
    (* simplified: type-conversion *)
    | ChangeInt31ToTaggedSigned ->
        let pid = Operands.id_of_nth operands 0 in
        let pval = RegisterFile.find pid rf in
        change_int31_to_taggedsigned vid pval
    | ChangeInt32ToTagged ->
        let pid = Operands.id_of_nth operands 0 in
        let pval = RegisterFile.find pid rf in
        change_int32_to_tagged vid pval mem
    | ChangeInt64ToTagged ->
        let pid = Operands.id_of_nth operands 0 in
        let pval = RegisterFile.find pid rf in
        change_int64_to_tagged vid pval mem
    | CheckedFloat64ToInt32 ->
        let pid = Operands.id_of_nth operands 0 in
        let pval = RegisterFile.find pid rf in
        checked_float64_to_int32 "" vid pval
    | CheckedTaggedSignedToInt32 ->
        let pid = Operands.id_of_nth operands 0 in
        let pval = RegisterFile.find pid rf in
        checked_tagged_signed_to_int32 vid pval
    (* machine: arithmetic *)
    | Float64Abs ->
        let pid = Operands.id_of_nth operands 0 in
        let pval = RegisterFile.find pid rf in
        float64_abs vid pval
    | Float64ExtractHighWord32 ->
        let pid = Operands.id_of_nth operands 0 in
        let pval = RegisterFile.find pid rf in
        float64_extract_high_word32 vid pval
    | Float64Sub ->
        let lpid = Operands.id_of_nth operands 0 in
        let rpid = Operands.id_of_nth operands 1 in
        let lval = RegisterFile.find lpid rf in
        let rval = RegisterFile.find rpid rf in
        float64_sub vid lval rval
    | Int32Add ->
        let lpid = Operands.id_of_nth operands 0 in
        let rpid = Operands.id_of_nth operands 1 in
        let lval = RegisterFile.find lpid rf in
        let rval = RegisterFile.find rpid rf in
        int32_add vid lval rval
    | Int32AddWithOverflow ->
        let lpid = Operands.id_of_nth operands 0 in
        let rpid = Operands.id_of_nth operands 1 in
        let lval = RegisterFile.find lpid rf in
        let rval = RegisterFile.find rpid rf in
        int32_add_with_overflow vid lval rval
    | Int32Mul ->
        let lpid = Operands.id_of_nth operands 0 in
        let rpid = Operands.id_of_nth operands 1 in
        let lval = RegisterFile.find lpid rf in
        let rval = RegisterFile.find rpid rf in
        int32_mul vid lval rval
    | Int32Sub ->
        let lpid = Operands.id_of_nth operands 0 in
        let rpid = Operands.id_of_nth operands 1 in
        let lval = RegisterFile.find lpid rf in
        let rval = RegisterFile.find rpid rf in
        int32_sub vid lval rval
    | Int64Add ->
        let lpid = Operands.id_of_nth operands 0 in
        let rpid = Operands.id_of_nth operands 1 in
        let lval = RegisterFile.find lpid rf in
        let rval = RegisterFile.find rpid rf in
        int64_add vid lval rval
    | Int64Sub ->
        let lpid = Operands.id_of_nth operands 0 in
        let rpid = Operands.id_of_nth operands 1 in
        let lval = RegisterFile.find lpid rf in
        let rval = RegisterFile.find rpid rf in
        int64_sub vid lval rval
    | Word32Sar ->
        let hint = Operands.const_of_nth operands 0 in
        let lpid = Operands.id_of_nth operands 1 in
        let rpid = Operands.id_of_nth operands 2 in
        let lval = RegisterFile.find lpid rf in
        let rval = RegisterFile.find rpid rf in
        word32_sar vid hint lval rval
    | Word32Shl ->
        let lpid = Operands.id_of_nth operands 0 in
        let rpid = Operands.id_of_nth operands 1 in
        let lval = RegisterFile.find lpid rf in
        let rval = RegisterFile.find rpid rf in
        word32_shl vid lval rval
    | Word32Xor ->
        let lpid = Operands.id_of_nth operands 0 in
        let rpid = Operands.id_of_nth operands 1 in
        let lval = RegisterFile.find lpid rf in
        let rval = RegisterFile.find rpid rf in
        word32_xor vid lval rval
    | Word64Shl ->
        let lpid = Operands.id_of_nth operands 0 in
        let rpid = Operands.id_of_nth operands 1 in
        let lval = RegisterFile.find lpid rf in
        let rval = RegisterFile.find rpid rf in
        word64_shl vid lval rval
    (* machine: logic *)
    | Float64Equal ->
        let lpid = Operands.id_of_nth operands 0 in
        let rpid = Operands.id_of_nth operands 1 in
        let lval = RegisterFile.find lpid rf in
        let rval = RegisterFile.find rpid rf in
        float64_equal vid lval rval
    | Float64LessThan ->
        let lpid = Operands.id_of_nth operands 0 in
        let rpid = Operands.id_of_nth operands 1 in
        let lval = RegisterFile.find lpid rf in
        let rval = RegisterFile.find rpid rf in
        float64_equal vid lval rval
    | Word32And ->
        let lpid = Operands.id_of_nth operands 0 in
        let rpid = Operands.id_of_nth operands 1 in
        let lval = RegisterFile.find lpid rf in
        let rval = RegisterFile.find rpid rf in
        word32_and vid lval rval
    | Word32Or ->
        let lpid = Operands.id_of_nth operands 0 in
        let rpid = Operands.id_of_nth operands 1 in
        let lval = RegisterFile.find lpid rf in
        let rval = RegisterFile.find rpid rf in
        word32_or vid lval rval
    (* machine: comparison *)
    | StackPointerGreaterThan -> (Value.tr, Control.empty, Bool.tr, Bool.fl)
    | Int32LessThan ->
        let lpid = Operands.id_of_nth operands 0 in
        let rpid = Operands.id_of_nth operands 1 in
        let lval = RegisterFile.find lpid rf in
        let rval = RegisterFile.find rpid rf in
        int32_less_than vid lval rval
    | Int64LessThan ->
        let lpid = Operands.id_of_nth operands 0 in
        let rpid = Operands.id_of_nth operands 1 in
        let lval = RegisterFile.find lpid rf in
        let rval = RegisterFile.find rpid rf in
        int32_less_than vid lval rval
    | Uint32LessThan ->
        let lpid = Operands.id_of_nth operands 0 in
        let rpid = Operands.id_of_nth operands 1 in
        let lval = RegisterFile.find lpid rf in
        let rval = RegisterFile.find rpid rf in
        uint32_less_than vid lval rval
    | Uint32LessThanOrEqual ->
        let lpid = Operands.id_of_nth operands 0 in
        let rpid = Operands.id_of_nth operands 1 in
        let lval = RegisterFile.find lpid rf in
        let rval = RegisterFile.find rpid rf in
        uint32_less_than_or_equal vid lval rval
    | Uint64LessThan ->
        let lpid = Operands.id_of_nth operands 0 in
        let rpid = Operands.id_of_nth operands 1 in
        let lval = RegisterFile.find lpid rf in
        let rval = RegisterFile.find rpid rf in
        uint64_less_than vid lval rval
    | Uint64LessThanOrEqual ->
        let lpid = Operands.id_of_nth operands 0 in
        let rpid = Operands.id_of_nth operands 1 in
        let lval = RegisterFile.find lpid rf in
        let rval = RegisterFile.find rpid rf in
        uint64_less_than_or_equal vid lval rval
    | Word32Equal ->
        let lpid = Operands.id_of_nth operands 0 in
        let rpid = Operands.id_of_nth operands 1 in
        let lval = RegisterFile.find lpid rf in
        let rval = RegisterFile.find rpid rf in
        word32_equal vid lval rval
    | Word64Equal ->
        let lpid = Operands.id_of_nth operands 0 in
        let rpid = Operands.id_of_nth operands 1 in
        let lval = RegisterFile.find lpid rf in
        let rval = RegisterFile.find rpid rf in
        word64_equal vid lval rval
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
        let repr = Operands.const_of_nth operands 2 |> Repr.of_rs_string in
        load vid ptr pos repr !mem
    (* machine: bitcast *)
    | BitcastFloat32ToInt32 ->
        let pid = Operands.id_of_nth operands 0 in
        let pval = RegisterFile.find pid rf in
        bitcast_float64_to_int64 vid pval
    | BitcastFloat64ToInt64 ->
        let pid = Operands.id_of_nth operands 0 in
        let pval = RegisterFile.find pid rf in
        bitcast_float64_to_int64 vid pval
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
    (* machine: type-conversion *)
    | ChangeInt32ToFloat64 ->
        let pid = Operands.id_of_nth operands 0 in
        let pval = RegisterFile.find pid rf in
        change_int32_to_float64 vid pval
    | ChangeFloat64ToInt64 ->
        let pid = Operands.id_of_nth operands 0 in
        let pval = RegisterFile.find pid rf in
        change_float64_to_int64 vid pval
    | ChangeInt64ToFloat64 ->
        let pid = Operands.id_of_nth operands 0 in
        let pval = RegisterFile.find pid rf in
        change_int64_to_float64 vid pval
    | ChangeUint32ToUint64 ->
        let pid = Operands.id_of_nth operands 0 in
        let pval = RegisterFile.find pid rf in
        change_uint32_to_uint64 vid pval
    | ChangeUint32ToFloat64 ->
        let pid = Operands.id_of_nth operands 0 in
        let pval = RegisterFile.find pid rf in
        change_uint32_to_float64 vid pval
    | RoundFloat64ToInt32 ->
        let pid = Operands.id_of_nth operands 0 in
        let pval = RegisterFile.find pid rf in
        round_float64_to_int32 vid pval
    | Empty -> (Value.empty, Control.empty, Bool.tr, Bool.fl)
    | _ ->
        let msg =
          Format.sprintf "unsupported instruction: %s" (opcode |> Opcode.to_str)
        in
        print_endline msg;
        (Value.empty, Control.empty, Bool.tr, Bool.fl)
  in

  let updated_asrt = Bool.ands [ State.assertion state; assertion ] in
  let type_is_verified =
    match ty with Some ty -> Typer.verify value ty mem | None -> Bool.tr
  in

  let updated_rf = RegisterFile.add vid value rf in
  let updated_cf = ControlFile.add cid control cf in
  let updated_ub = Bool.ors [ State.ub state; ub; Bool.not type_is_verified ] in
  let next_state =
    State.update next_pc updated_cf updated_rf !mem updated_asrt updated_ub
      state
  in

  if State.is_end next_state then { next_state with retvar = Some value }
  else next program next_state cfg

(* execute the program and retrieve a final state *)
let execute program nparams stage cfg =
  (* symbols for parameters *)
  let init_state = State.init nparams stage in
  next program init_state cfg

let print_counter_example program state model =
  Format.printf "State of %s\n" (State.stage state);
  let rf = State.register_file state in
  let cf = State.control_file state in
  let rec aux pc =
    let _, opcode, operands = IR.instr_of pc program in
    let instr_s =
      Format.sprintf "%s(%s)" (opcode |> Opcode.to_str)
        (operands |> Operands.to_str)
    in

    let prefix = if State.stage state = "before" then "b" else "a" in
    RegisterFile.prefix := prefix ^ "v";
    ControlFile.prefix := prefix ^ "c";

    let value = RegisterFile.find (string_of_int pc) rf in
    let control = ControlFile.find (string_of_int pc) cf in

    Format.printf "#%d:%s => \n  Value: %s\n  Control: %s\n" pc instr_s
      (Model.eval model value false |> Option.get |> Expr.to_string)
      (Model.eval model control false |> Option.get |> Expr.to_string);

    match opcode with End -> Format.printf "\n" | _ -> aux (pc + 1)
  in
  aux 0

let run nparams src_program tgt_program before_cfg after_cfg =
  let src_state = execute src_program nparams "before" before_cfg in
  let tgt_state = execute tgt_program nparams "after" after_cfg in

  let retvar_is_same =
    Bool.eq
      (State.retvar src_state |> Option.get)
      (State.retvar tgt_state |> Option.get)
  in
  let ub_is_same = Bool.eq (State.ub src_state) (State.ub tgt_state) in
  let is_refined = Bool.ands [ retvar_is_same; ub_is_same ] in

  let assertion =
    Bool.ands
      [
        State.assertion src_state;
        State.assertion tgt_state;
        Bool.not is_refined;
      ]
  in

  let status = Solver.check validator assertion in
  match status with
  | SATISFIABLE ->
      let model = Option.get (Solver.get_model validator) in
      Printf.printf "\nResult: Not Verified \n";
      Printf.printf "CounterExample: \n";
      Params.print_evaluated model (State.params src_state);

      print_counter_example src_program src_state model;
      print_counter_example tgt_program tgt_state model
  | UNSATISFIABLE -> Printf.printf "\nResult: Verified\n"
  (* Printf.printf "Assertion: \n%s\n\n" (assertion |> str_of_simplified) *)
  | _ -> failwith "unknown"
