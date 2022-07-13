module Params = State.Params
module ControlFile = Control.ControlFile
module UBFile = Ub.UBFile
module HeapNumber = Objects.HeapNumber
open Common
open Simplified
open Machine
open Z3utils

let ctx = Z3utils.ctx

let validator =
  let tactic = Tactic.and_then [ "simplify"; "eq2bv"; "fpa2bv"; "qfaufbv" ] in
  Solver.init_with_tactic tactic

let tag base_is_tagged =
  match base_is_tagged with
  | "tagged base" -> 1
  | "untagged base" -> 0
  | _ -> failwith (Printf.sprintf "invalid input: %s" base_is_tagged)

let update_deopt (opcode : Opcode.t) operands rf control deopt =
  match opcode with
  | Deoptimize -> Bool.ands [ control; deopt ]
  | DeoptimizeIf ->
      let cond_id = Operands.id_of_nth operands 0 in
      let cond = RegisterFile.find cond_id rf |> Value.to_bool in
      Bool.ands [ control; cond; deopt ]
  | DeoptimizeUnless ->
      let cond_id = Operands.id_of_nth operands 0 in
      let cond = RegisterFile.find cond_id rf |> Value.to_bool in
      Bool.ands [ control; Bool.not cond; deopt ]
  | _ -> deopt

let rec next program state =
  let pc = State.pc state in
  let cf = State.control_file state in
  let rf = State.register_file state in
  let uf = State.ub_file state in
  let next_bid = ref (State.next_bid state) in
  let mem = ref (State.memory state) in
  let params = State.params state in
  let node_id = string_of_int pc in
  let vid = RegisterFile.vid node_id in
  let cid = ControlFile.cid node_id in
  let uid = UBFile.uid node_id in

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
        external_constant vid c
    | Int32Constant ->
        let c = Operands.const_of_nth operands 0 |> Value.from_istring in
        int32_constant vid c
    | Int64Constant ->
        let c = Operands.const_of_nth operands 0 |> Value.from_istring in
        int64_constant vid c
    | NumberConstant ->
        let c_str = Operands.const_of_nth operands 0 in
        number_constant vid c_str next_bid mem
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
        let ctrl_token = ControlFile.find nid cf in
        if_false cid ctrl_token
    | IfTrue ->
        let nid = Operands.id_of_nth operands 0 in
        let ctrl_token = ControlFile.find nid cf in
        if_true cid ctrl_token
    | Phi -> (
        let rev = operands |> List.rev in
        let ctrl_id = Operands.id_of_nth rev 0 in
        let _, ctrl_opcode, incomings_id =
          IR.instr_of (ctrl_id |> int_of_string) program
        in
        match ctrl_opcode with
        | Merge ->
            let incoming_ctrl_tokens =
              ControlFile.find_all (incomings_id |> Operands.id_of_all) cf
            in
            let repr =
              Operands.const_of_nth rev 1 |> MachineType.Repr.of_string
            in
            let incoming_values =
              RegisterFile.find_all
                (rev |> List.tl |> List.tl |> List.rev |> Operands.id_of_all)
                rf
            in
            phi vid incoming_values repr incoming_ctrl_tokens
        | Dead -> (Value.empty, Control.empty, Bool.tr, Bool.fl)
        | _ ->
            failwith
              (Format.sprintf "Phi is not implemented for incoming opcode: %s"
                 (ctrl_opcode |> Opcode.to_str)))
    | Select ->
        let cond_id = Operands.id_of_nth operands 0 in
        let true_id = Operands.id_of_nth operands 1 in
        let false_id = Operands.id_of_nth operands 2 in
        let cond_value = RegisterFile.find cond_id rf in
        let true_value = RegisterFile.find true_id rf in
        let false_value = RegisterFile.find false_id rf in
        select vid cond_value true_value false_value
    | Start -> start cid
    | Throw ->
        let nid = Operands.id_of_nth operands 0 in
        let ctrl_token = ControlFile.find nid cf in
        throw cid ctrl_token
    | Merge ->
        let conds = ControlFile.find_all (operands |> Operands.id_of_all) cf in
        merge cid conds
    | Unreachable ->
        let cid = Operands.id_of_nth operands 0 in
        let ctrl_token = ControlFile.find cid cf in
        (Value.empty, Control.empty, Bool.tr, ctrl_token)
    (* common: deoptimization *)
    | DeoptimizeUnless -> (Value.empty, Bool.tr, Bool.tr, Bool.fl)
    (* common: dead *)
    | Dead -> (Value.empty, Control.empty, Bool.tr, Bool.fl)
    (* common: procedure *)
    | Parameter ->
        let pidx = Operands.const_of_nth operands 0 |> int_of_string in
        if 0 < pidx && pidx <= List.length params then
          let param = List.nth params (pidx - 1) in
          parameter vid param !mem
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
    (* JS: comparision *)
    | JSStackCheck -> (Value.empty, Bool.tr, Bool.tr, Bool.fl)
    (* simplified: numeric *)
    | NumberAdd ->
        let lpid = Operands.id_of_nth operands 0 in
        let rpid = Operands.id_of_nth operands 1 in
        let lval = RegisterFile.find lpid rf in
        let rval = RegisterFile.find rpid rf in
        number_add vid lval rval next_bid mem
    | NumberAbs ->
        let pid = Operands.id_of_nth operands 0 in
        let pval = RegisterFile.find pid rf in
        number_abs vid pval next_bid mem
    | NumberExpm1 ->
        let pid = Operands.id_of_nth operands 0 in
        let pval = RegisterFile.find pid rf in
        number_expm1 vid pval next_bid mem
    | NumberMax ->
        let lpid = Operands.id_of_nth operands 0 in
        let rpid = Operands.id_of_nth operands 1 in
        let lval = RegisterFile.find lpid rf in
        let rval = RegisterFile.find rpid rf in
        number_max vid lval rval next_bid mem
    | NumberMin ->
        let lpid = Operands.id_of_nth operands 0 in
        let rpid = Operands.id_of_nth operands 1 in
        let lval = RegisterFile.find lpid rf in
        let rval = RegisterFile.find rpid rf in
        number_min vid lval rval next_bid mem
    | NumberMultiply ->
        let lpid = Operands.id_of_nth operands 0 in
        let rpid = Operands.id_of_nth operands 1 in
        let lval = RegisterFile.find lpid rf in
        let rval = RegisterFile.find rpid rf in
        number_multiply vid lval rval next_bid mem
    | SpeculativeNumberAdd ->
        let lpid = Operands.id_of_nth operands 0 in
        let rpid = Operands.id_of_nth operands 1 in
        let lval = RegisterFile.find lpid rf in
        let rval = RegisterFile.find rpid rf in
        speculative_number_add vid lval rval next_bid mem
    | SpeculativeNumberMultiply ->
        let lpid = Operands.id_of_nth operands 0 in
        let rpid = Operands.id_of_nth operands 1 in
        let lval = RegisterFile.find lpid rf in
        let rval = RegisterFile.find rpid rf in
        speculative_number_multiply vid lval rval next_bid mem
    | SpeculativeSafeIntegerAdd ->
        let lpid = Operands.id_of_nth operands 0 in
        let rpid = Operands.id_of_nth operands 1 in
        let lval = RegisterFile.find lpid rf in
        let rval = RegisterFile.find rpid rf in
        speculative_safe_integer_add vid lval rval next_bid mem
    | SpeculativeSafeIntegerSubtract ->
        let lpid = Operands.id_of_nth operands 0 in
        let rpid = Operands.id_of_nth operands 1 in
        let lval = RegisterFile.find lpid rf in
        let rval = RegisterFile.find rpid rf in
        speculative_safe_integer_subtract vid lval rval next_bid mem
    (* simplified: bitwise *)
    | BooleanNot ->
        let pid = Operands.id_of_nth operands 0 in
        let pval = RegisterFile.find pid rf in
        boolean_not vid pval
    | SpeculativeNumberBitwiseOr ->
        let lpid = Operands.id_of_nth operands 0 in
        let rpid = Operands.id_of_nth operands 1 in
        let lval = RegisterFile.find lpid rf in
        let rval = RegisterFile.find rpid rf in
        speculative_number_bitwise_or vid lval rval next_bid mem
    | SpeculativeNumberBitwiseXor ->
        let lpid = Operands.id_of_nth operands 0 in
        let rpid = Operands.id_of_nth operands 1 in
        let lval = RegisterFile.find lpid rf in
        let rval = RegisterFile.find rpid rf in
        speculative_number_bitwise_xor vid lval rval
    (* simplified: comparison *)
    | NumberLessThan ->
        let lpid = Operands.id_of_nth operands 0 in
        let rpid = Operands.id_of_nth operands 1 in
        let lval = RegisterFile.find lpid rf in
        let rval = RegisterFile.find rpid rf in
        number_less_than vid lval rval next_bid mem
    | SpeculativeNumberEqual ->
        let lpid = Operands.id_of_nth operands 0 in
        let rpid = Operands.id_of_nth operands 1 in
        let lval = RegisterFile.find lpid rf in
        let rval = RegisterFile.find rpid rf in
        speculative_number_equal vid lval rval next_bid mem
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
        allocate_raw vid cid size_value next_bid ct
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
    | LoadField ->
        let base_is_tagged = Operands.const_of_nth operands 0 in
        let tag_value = tag base_is_tagged in
        let offset = Operands.const_of_nth operands 1 |> int_of_string in
        let machine_type = Operands.const_of_nth operands 2 in
        let repr = MachineType.Repr.of_rs_string machine_type in
        let bid_id = Operands.id_of_nth operands 3 in
        let bid = RegisterFile.find bid_id rf in
        load_field vid tag_value offset repr bid !mem
    | LoadTypedElement ->
        let array_type = Operands.const_of_nth operands 0 |> int_of_string in
        let base_id = Operands.id_of_nth operands 1 in
        let base = RegisterFile.find base_id rf in
        let extern_id = Operands.id_of_nth operands 2 in
        let extern = RegisterFile.find extern_id rf in
        let ind_id = Operands.id_of_nth operands 3 in
        let ind = RegisterFile.find ind_id rf in
        load_typed_element vid array_type base extern ind !mem
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
    | ChangeBitToTagged ->
        let pid = Operands.id_of_nth operands 0 in
        let pval = RegisterFile.find pid rf in
        change_bit_to_tagged vid pval next_bid mem
    | ChangeInt31ToTaggedSigned ->
        let pid = Operands.id_of_nth operands 0 in
        let pval = RegisterFile.find pid rf in
        change_int31_to_taggedsigned vid pval
    | ChangeInt32ToTagged ->
        let pid = Operands.id_of_nth operands 0 in
        let pval = RegisterFile.find pid rf in
        change_int32_to_tagged vid pval next_bid mem
    | ChangeInt64ToTagged ->
        let pid = Operands.id_of_nth operands 0 in
        let pval = RegisterFile.find pid rf in
        change_int64_to_tagged vid pval next_bid mem
    | CheckedFloat64ToInt32 ->
        let hint = Operands.const_of_nth operands 0 in
        let pid = Operands.id_of_nth operands 1 in
        let pval = RegisterFile.find pid rf in
        checked_float64_to_int32 hint vid pval
    | CheckedTaggedSignedToInt32 ->
        let pid = Operands.id_of_nth operands 0 in
        let pval = RegisterFile.find pid rf in
        checked_tagged_signed_to_int32 vid pval
    | NumberToInt32 ->
        let pid = Operands.id_of_nth operands 0 in
        let pval = RegisterFile.find pid rf in
        number_to_int32 vid pval next_bid mem
    | SpeculativeToNumber ->
        let pid = Operands.id_of_nth operands 0 in
        let pval = RegisterFile.find pid rf in
        speculative_to_number vid pval next_bid mem
    | ToBoolean ->
        let pid = Operands.id_of_nth operands 0 in
        let pval = RegisterFile.find pid rf in
        to_boolean vid pval mem
    | TruncateTaggedToBit ->
        let pid = Operands.id_of_nth operands 0 in
        let pval = RegisterFile.find pid rf in
        truncate_tagged_to_bit vid pval mem
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
    | Word32Shr ->
        let lpid = Operands.id_of_nth operands 0 in
        let rpid = Operands.id_of_nth operands 1 in
        let lval = RegisterFile.find lpid rf in
        let rval = RegisterFile.find rpid rf in
        word32_shr vid lval rval
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
        float64_less_than vid lval rval
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
        (* let msg =
             Format.sprintf "unsupported instruction: %s" (opcode |> Opcode.to_str)
           in
           print_endline msg; *)
        (Value.empty, Control.empty, Bool.tr, Bool.fl)
  in

  let propagated_ub =
    let type_is_verified =
      match ty with Some ty -> Typer.verify value ty mem | None -> Bool.tr
    in
    let ub_from_input =
      match opcode with
      | Merge ->
          let pids = operands |> Operands.id_of_all in
          let conds = ControlFile.find_all pids cf in
          let ubs = UBFile.find_all pids uf in
          Bool.ors
            (List.rev_map2 (fun cond ub -> Bool.ands [ cond; ub ]) conds ubs)
      | Phi -> (
          let rev = operands |> List.rev in
          let ctrl_id = Operands.id_of_nth rev 0 in
          let ctrl_ub = UBFile.find ctrl_id uf in
          let _, ctrl_opcode, incomings_id =
            IR.instr_of (ctrl_id |> int_of_string) program
          in
          match ctrl_opcode with
          | Merge ->
              let incoming_ctrl_tokens =
                ControlFile.find_all (incomings_id |> Operands.id_of_all) cf
              in
              let incoming_ubs =
                UBFile.find_all
                  (rev |> List.tl |> List.tl |> List.rev |> Operands.id_of_all)
                  uf
              in
              Bool.ors
                (ctrl_ub
                :: List.rev_map2
                     (fun ctrl ub -> Bool.ands [ ctrl; ub ])
                     incoming_ctrl_tokens incoming_ubs)
          | Dead -> Bool.tr
          | _ ->
              failwith
                (Format.sprintf "Phi is not implemented for incoming opcode: %s"
                   (ctrl_opcode |> Opcode.to_str)))
      | _ ->
          let pids = Operands.id_of_all operands in
          let ubs = UBFile.find_all pids uf in
          Bool.ors ubs
    in
    Bool.ors [ ub; ub_from_input; Bool.not type_is_verified ]
  in

  (* update state *)
  let updated_asrt = Bool.ands [ State.assertion state; assertion ] in
  let updated_rf = RegisterFile.add vid value rf in
  let updated_cf = ControlFile.add cid control cf in
  let updated_uf = UBFile.add uid propagated_ub uf in
  let updated_deopt =
    update_deopt opcode operands rf control (State.deopt state)
  in
  let next_state =
    State.update next_pc !next_bid updated_cf updated_rf updated_uf !mem
      updated_asrt updated_deopt state
  in

  if State.is_end next_state then
    { next_state with retval = value; ub = propagated_ub }
  else next program next_state

(* execute the program and retrieve a final state *)
let execute stage program nparams =
  (* symbols for parameters *)
  let init_state = State.init nparams stage in
  next program init_state

let check_ub_semantic nparams program =
  let state = execute "test" program nparams in
  let ub = State.ub state in
  let precond = Bool.not (State.deopt state) in
  let assertion = Bool.ands [ State.assertion state; precond; ub ] in
  let status = Solver.check validator assertion in

  match status with
  | SATISFIABLE ->
      let model = Option.get (Solver.get_model validator) in
      Printf.printf "Result: Not Verified\n";
      Printf.printf "UB: %s\n" (Model.eval model ub |> Expr.to_simplified_string);
      Printf.printf "CounterExample: \n";
      Printer.print_params model (State.memory state) (State.params state);
      Printer.print_counter_example program state model
  | UNSATISFIABLE -> Printf.printf "Result: Verified\n"
  | UNKNOWN ->
      let reason = Z3.Solver.get_reason_unknown validator in
      Printf.printf "Result: Unknown\nReason: %s" reason

let run nparams src_program tgt_program =
  let src_state = execute "before" src_program nparams in
  let tgt_state = execute "after" tgt_program nparams in

  (* assume return value is either smi or heap number. *)
  let retval_is_same =
    let src_retval = State.retval src_state in
    let tgt_retval = State.retval tgt_state in
    let src_mem = State.memory src_state in
    let tgt_mem = State.memory tgt_state in
    let to_float64 value mem =
      Bool.ite
        (value |> Value.has_type Type.tagged_signed)
        (* if smi *)
        (value |> Value.TaggedSigned.to_float64)
        (* else if heap number *)
        (HeapNumber.load value mem |> HeapNumber.to_float64)
    in
    Bool.eq (to_float64 src_retval src_mem) (to_float64 tgt_retval tgt_mem)
  in

  let src_ub = State.ub src_state in
  let tgt_ub = State.ub tgt_state in
  let ub_is_same = Bool.eq src_ub tgt_ub in
  let is_refined =
    Bool.ite ub_is_same
      (Bool.ite (Bool.eq src_ub Bool.tr) Bool.tr retval_is_same)
      Bool.fl
  in

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
      Printf.printf "Result: Not Verified \n";
      Printf.printf "  ub is same: %s\n"
        (Model.eval model ub_is_same |> Expr.to_string);
      Printf.printf "    src ub: %s\n"
        (Model.eval model (State.ub src_state) |> Expr.to_string);
      Printf.printf "    tgt ub: %s\n"
        (Model.eval model (State.ub tgt_state) |> Expr.to_string);
      Printf.printf "  retvar is same: %s\n"
        (Model.eval model retval_is_same |> Expr.to_string);
      Printf.printf "CounterExample: \n";
      Printer.print_params model (State.memory src_state)
        (State.params src_state);
      Printer.print_counter_example src_program src_state model;
      Printer.print_counter_example tgt_program tgt_state model
  | UNSATISFIABLE -> Printf.printf "Result: Verified\n"
  | UNKNOWN ->
      let reason = Z3.Solver.get_reason_unknown validator in
      Printf.printf "Result: Unknown\nReason: %s" reason
