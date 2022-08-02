module Params = State.Params
module DeoptFile = State.DeoptFile
module UBFile = State.UBFile
module HeapNumber = Objects.HeapNumber
open ValueOperator
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

let encode program
    ({
       State.pc;
       control_file = cf;
       register_file = rf;
       memory = mem;
       params;
       next_bid;
       _;
     } as state) =
  let nop state = state in

  let _, opcode, operands = IR.instr_of pc program in
  let encode_machine_unary op =
    let pid = Operands.id_of_nth operands 0 in
    let pval = RegisterFile.find pid rf in
    op pval
  in

  let encode_machine_binary op =
    let lpid = Operands.id_of_nth operands 0 in
    let rpid = Operands.id_of_nth operands 1 in
    let lval = RegisterFile.find lpid rf in
    let rval = RegisterFile.find rpid rf in
    op lval rval
  in

  let encode_machine_ovf op =
    let lpid = Operands.id_of_nth operands 0 in
    let rpid = Operands.id_of_nth operands 1 in
    let cid = Operands.id_of_nth operands 2 in
    let lval = RegisterFile.find lpid rf in
    let rval = RegisterFile.find rpid rf in
    let ctrl = ControlFile.find cid cf in
    op lval rval ctrl
  in

  let encode_machine_binary_with_hint op =
    let hint = Operands.const_of_nth operands 0 in
    let lpid = Operands.id_of_nth operands 1 in
    let rpid = Operands.id_of_nth operands 2 in
    let lval = RegisterFile.find lpid rf in
    let rval = RegisterFile.find rpid rf in
    op hint lval rval
  in

  let encode_checked_simplified_binary_with_hint op =
    let hint = Operands.const_of_nth operands 0 in
    let lpid = Operands.id_of_nth operands 1 in
    let rpid = Operands.id_of_nth operands 2 in
    let _eid = Operands.id_of_nth operands 3 in
    let cid = Operands.id_of_nth operands 4 in
    let lval = RegisterFile.find lpid rf in
    let rval = RegisterFile.find rpid rf in
    let ctrl = ControlFile.find cid cf in
    op hint lval rval () ctrl
  in

  let encode_checked_simplified_binary op =
    let lpid = Operands.id_of_nth operands 0 in
    let rpid = Operands.id_of_nth operands 1 in
    let _eid = Operands.id_of_nth operands 2 in
    let cid = Operands.id_of_nth operands 3 in
    let lval = RegisterFile.find lpid rf in
    let rval = RegisterFile.find rpid rf in
    let ctrl = ControlFile.find cid cf in
    op lval rval () ctrl
  in

  state
  |>
  match opcode with
  (* common: constants *)
  | Float64Constant ->
      let c =
        Operands.const_of_nth operands 0
        |> Value.from_f64string |> Value.cast Type.float64
      in
      float64_constant c
  | HeapConstant ->
      let addr_name_re = Re.Pcre.regexp "(0x[0-9a-f]+) <([^>]*)>" in
      let operand = Operands.const_of_nth operands 0 in
      let addr_name = Re.exec addr_name_re operand in
      let ptr =
        Re.Group.get addr_name 1 |> BitVecVal.from_istring
        |> Value.entype Type.pointer
      in
      let name = Re.Group.get addr_name 2 in
      (* if constant is default constant, use pre-defined value in register file *)
      if List.mem name State.default_constants then
        heap_constant (RegisterFile.find name rf)
      else heap_constant ptr
  | ExternalConstant ->
      let addr_re = Re.Pcre.regexp "(0x[0-9a-f]+)" in
      let operand = Operands.const_of_nth operands 0 in
      let c =
        Re.Group.get (Re.exec addr_re operand) 1
        |> BitVecVal.from_istring |> Value.entype Type.pointer
      in
      external_constant c
  | Int32Constant ->
      let c = Operands.const_of_nth operands 0 |> BitVecVal.from_istring in
      int32_constant c
  | Int64Constant ->
      let c = Operands.const_of_nth operands 0 |> BitVecVal.from_istring in
      int64_constant c
  | NumberConstant ->
      let c_str = Operands.const_of_nth operands 0 in
      number_constant c_str
  (* common: control *)
  | Projection ->
      let idx = Operands.const_of_nth operands 0 |> int_of_string in
      let id = Operands.id_of_nth operands 1 in
      let incoming = RegisterFile.find id rf in
      projection idx incoming
  | Branch ->
      let cond_id = Operands.id_of_nth operands 0 in
      let prev_id = Operands.id_of_nth operands 1 in
      let cond_value = RegisterFile.find cond_id rf in
      let precond_token = ControlFile.find prev_id cf in
      branch cond_value precond_token
  | IfFalse ->
      let nid = Operands.id_of_nth operands 0 in
      let ctrl_token = ControlFile.find nid cf in
      if_false ctrl_token
  | IfTrue ->
      let nid = Operands.id_of_nth operands 0 in
      let ctrl_token = ControlFile.find nid cf in
      if_true ctrl_token
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
          phi incoming_values repr incoming_ctrl_tokens
      | Dead -> nop
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
      select cond_value true_value false_value
  | Start -> start
  | Throw ->
      let nid = Operands.id_of_nth operands 0 in
      let ctrl_token = ControlFile.find nid cf in
      throw ctrl_token
  | Merge ->
      let conds = ControlFile.find_all (operands |> Operands.id_of_all) cf in
      merge conds
  | Unreachable ->
      let cid = Operands.id_of_nth operands 1 in
      let control = ControlFile.find cid cf in
      unreachable control
  (* common: deoptimization *)
  | DeoptimizeIf ->
      let cond_id = Operands.id_of_nth operands 0 in
      (* let frame_id = Operands.id_of_nth operands 1 in
         let eff_id = Operands.id_of_nth operands 2 in *)
      let ctrl_id = Operands.id_of_nth operands 3 in
      let deopt_cond = RegisterFile.find cond_id rf in
      let ctrl = ControlFile.find ctrl_id cf in
      deoptimize_if deopt_cond () () ctrl
  | DeoptimizeUnless ->
      let cond_id = Operands.id_of_nth operands 0 in
      let ct_id = Operands.id_of_nth operands 3 in
      let cond = RegisterFile.find cond_id rf in
      let ct = ControlFile.find ct_id cf in
      deoptimize_unless cond () () ct
  (* common: dead *)
  | Dead -> nop
  (* common: procedure *)
  | Parameter ->
      let pidx = Operands.const_of_nth operands 0 |> int_of_string in
      if 0 < pidx && pidx <= List.length params then
        let param = List.nth params (pidx - 1) in
        parameter param
      else nop
  | Call -> call
  | Return ->
      let pid = Operands.id_of_nth operands 0 in
      let cid = Operands.id_of_nth operands 1 in
      let retval = RegisterFile.find pid rf in
      let retctrl = ControlFile.find cid cf in
      return retval retctrl next_bid mem
  | End ->
      let retvals = RegisterFile.find_all (operands |> Operands.id_of_all) rf in
      let retctrls = ControlFile.find_all (operands |> Operands.id_of_all) cf in
      end_ retvals () retctrls
  (* common: region *)
  | FinishRegion ->
      let pid = Operands.id_of_nth operands 0 in
      let pval = RegisterFile.find pid rf in
      finish_region pval
  (* JS: comparision *)
  | JSStackCheck -> js_stack_check
  (* simplified: numeric *)
  | CheckedInt32Add -> encode_checked_simplified_binary checked_int32_add
  | CheckedInt32Div -> encode_checked_simplified_binary checked_int32_div
  | CheckedInt32Mul ->
      encode_checked_simplified_binary_with_hint checked_int32_mul
  | CheckedInt32Sub -> encode_checked_simplified_binary checked_int32_sub
  | CheckedUint32Div -> encode_checked_simplified_binary checked_uint32_div
  | NumberAdd ->
      let lpid = Operands.id_of_nth operands 0 in
      let rpid = Operands.id_of_nth operands 1 in
      let lval = RegisterFile.find lpid rf in
      let rval = RegisterFile.find rpid rf in
      number_add lval rval mem
  | NumberAbs ->
      let pid = Operands.id_of_nth operands 0 in
      let pval = RegisterFile.find pid rf in
      number_abs pval mem
  | NumberCeil ->
      let pid = Operands.id_of_nth operands 0 in
      let pval = RegisterFile.find pid rf in
      number_ceil pval mem
  | NumberDivide ->
      let lpid = Operands.id_of_nth operands 0 in
      let rpid = Operands.id_of_nth operands 1 in
      let lval = RegisterFile.find lpid rf in
      let rval = RegisterFile.find rpid rf in
      number_divide lval rval mem
  | NumberImul ->
      let lpid = Operands.id_of_nth operands 0 in
      let rpid = Operands.id_of_nth operands 1 in
      let lval = RegisterFile.find lpid rf in
      let rval = RegisterFile.find rpid rf in
      number_imul lval rval mem
  | NumberExpm1 ->
      let pid = Operands.id_of_nth operands 0 in
      let pval = RegisterFile.find pid rf in
      number_expm1 pval mem
  | NumberFloor ->
      let pid = Operands.id_of_nth operands 0 in
      let pval = RegisterFile.find pid rf in
      number_floor pval mem
  | NumberMax ->
      let lpid = Operands.id_of_nth operands 0 in
      let rpid = Operands.id_of_nth operands 1 in
      let lval = RegisterFile.find lpid rf in
      let rval = RegisterFile.find rpid rf in
      number_max lval rval next_bid mem
  | NumberMin ->
      let lpid = Operands.id_of_nth operands 0 in
      let rpid = Operands.id_of_nth operands 1 in
      let lval = RegisterFile.find lpid rf in
      let rval = RegisterFile.find rpid rf in
      number_min lval rval next_bid mem
  | NumberMultiply ->
      let lpid = Operands.id_of_nth operands 0 in
      let rpid = Operands.id_of_nth operands 1 in
      let lval = RegisterFile.find lpid rf in
      let rval = RegisterFile.find rpid rf in
      number_multiply lval rval next_bid mem
  | NumberModulus ->
      let lpid = Operands.id_of_nth operands 0 in
      let rpid = Operands.id_of_nth operands 1 in
      let lval = RegisterFile.find lpid rf in
      let rval = RegisterFile.find rpid rf in
      number_modulus lval rval mem
  | NumberRound ->
      let pid = Operands.id_of_nth operands 0 in
      let pval = RegisterFile.find pid rf in
      number_round pval mem
  | NumberSign ->
      let pid = Operands.id_of_nth operands 0 in
      let pval = RegisterFile.find pid rf in
      number_sign pval mem
  | NumberSin ->
      let pid = Operands.id_of_nth operands 0 in
      let pval = RegisterFile.find pid rf in
      number_sign pval mem
  | NumberSubtract ->
      let lpid = Operands.id_of_nth operands 0 in
      let rpid = Operands.id_of_nth operands 1 in
      let lval = RegisterFile.find lpid rf in
      let rval = RegisterFile.find rpid rf in
      number_subtract lval rval mem
  | NumberTrunc ->
      let pid = Operands.id_of_nth operands 0 in
      let pval = RegisterFile.find pid rf in
      number_trunc pval mem
  | SpeculativeNumberAdd ->
      let lpid = Operands.id_of_nth operands 0 in
      let rpid = Operands.id_of_nth operands 1 in
      let lval = RegisterFile.find lpid rf in
      let rval = RegisterFile.find rpid rf in
      speculative_number_add lval rval mem
  | SpeculativeNumberDivide ->
      let lpid = Operands.id_of_nth operands 0 in
      let rpid = Operands.id_of_nth operands 1 in
      let ctrl_id = Operands.id_of_nth operands 3 in
      let lval = RegisterFile.find lpid rf in
      let rval = RegisterFile.find rpid rf in
      let ctrl = ControlFile.find ctrl_id cf in
      speculative_number_divide lval rval () ctrl mem
  | SpeculativeNumberModulus ->
      let lpid = Operands.id_of_nth operands 0 in
      let rpid = Operands.id_of_nth operands 1 in
      let ctrl_id = Operands.id_of_nth operands 3 in
      let lval = RegisterFile.find lpid rf in
      let rval = RegisterFile.find rpid rf in
      let ctrl = ControlFile.find ctrl_id cf in
      speculative_number_modulus lval rval () ctrl mem
  | SpeculativeNumberMultiply ->
      let lpid = Operands.id_of_nth operands 0 in
      let rpid = Operands.id_of_nth operands 1 in
      let lval = RegisterFile.find lpid rf in
      let rval = RegisterFile.find rpid rf in
      speculative_number_multiply lval rval next_bid mem
  | SpeculativeNumberSubtract ->
      let lpid = Operands.id_of_nth operands 0 in
      let rpid = Operands.id_of_nth operands 1 in
      let ctrl_id = Operands.id_of_nth operands 3 in
      let lval = RegisterFile.find lpid rf in
      let rval = RegisterFile.find rpid rf in
      let ctrl = ControlFile.find ctrl_id cf in
      speculative_number_subtract lval rval () ctrl mem
  | SpeculativeSafeIntegerAdd ->
      let lpid = Operands.id_of_nth operands 0 in
      let rpid = Operands.id_of_nth operands 1 in
      let lval = RegisterFile.find lpid rf in
      let rval = RegisterFile.find rpid rf in
      speculative_safe_integer_add lval rval next_bid mem
  | SpeculativeSafeIntegerSubtract ->
      let lpid = Operands.id_of_nth operands 0 in
      let rpid = Operands.id_of_nth operands 1 in
      let lval = RegisterFile.find lpid rf in
      let rval = RegisterFile.find rpid rf in
      speculative_safe_integer_subtract lval rval next_bid mem
  (* simplified: bitwise *)
  | BooleanNot ->
      let pid = Operands.id_of_nth operands 0 in
      let pval = RegisterFile.find pid rf in
      boolean_not pval
  | NumberShiftRightLogical ->
      let lpid = Operands.id_of_nth operands 0 in
      let rpid = Operands.id_of_nth operands 1 in
      let lval = RegisterFile.find lpid rf in
      let rval = RegisterFile.find rpid rf in
      number_shift_right_logical lval rval mem
  | SpeculativeNumberBitwiseOr ->
      let lpid = Operands.id_of_nth operands 0 in
      let rpid = Operands.id_of_nth operands 1 in
      let lval = RegisterFile.find lpid rf in
      let rval = RegisterFile.find rpid rf in
      speculative_number_bitwise_or lval rval next_bid mem
  | SpeculativeNumberBitwiseXor ->
      let lpid = Operands.id_of_nth operands 0 in
      let rpid = Operands.id_of_nth operands 1 in
      let lval = RegisterFile.find lpid rf in
      let rval = RegisterFile.find rpid rf in
      speculative_number_bitwise_xor lval rval
  | SpeculativeNumberShiftRightLogical ->
      let lpid = Operands.id_of_nth operands 0 in
      let rpid = Operands.id_of_nth operands 1 in
      let ctrl_id = Operands.id_of_nth operands 3 in
      let lval = RegisterFile.find lpid rf in
      let rval = RegisterFile.find rpid rf in
      let ctrl = ControlFile.find ctrl_id cf in
      speculative_number_shift_right_logical lval rval () ctrl mem
  (* simplified: comparison *)
  | NumberEqual ->
      let lpid = Operands.id_of_nth operands 0 in
      let rpid = Operands.id_of_nth operands 1 in
      let lval = RegisterFile.find lpid rf in
      let rval = RegisterFile.find rpid rf in
      number_equal lval rval mem
  | NumberLessThan ->
      let lpid = Operands.id_of_nth operands 0 in
      let rpid = Operands.id_of_nth operands 1 in
      let lval = RegisterFile.find lpid rf in
      let rval = RegisterFile.find rpid rf in
      number_less_than lval rval mem
  | NumberLessThanOrEqual ->
      let lpid = Operands.id_of_nth operands 0 in
      let rpid = Operands.id_of_nth operands 1 in
      let lval = RegisterFile.find lpid rf in
      let rval = RegisterFile.find rpid rf in
      number_less_than_or_equal lval rval mem
  | ReferenceEqual ->
      let lpid = Operands.id_of_nth operands 0 in
      let rpid = Operands.id_of_nth operands 1 in
      let lval = RegisterFile.find lpid rf in
      let rval = RegisterFile.find rpid rf in
      word32_equal lval rval
  | SpeculativeNumberEqual ->
      let lpid = Operands.id_of_nth operands 0 in
      let rpid = Operands.id_of_nth operands 1 in
      let lval = RegisterFile.find lpid rf in
      let rval = RegisterFile.find rpid rf in
      speculative_number_equal lval rval mem
  | SpeculativeNumberLessThan ->
      let lpid = Operands.id_of_nth operands 0 in
      let rpid = Operands.id_of_nth operands 1 in
      let ctrl_id = Operands.id_of_nth operands 3 in
      let lval = RegisterFile.find lpid rf in
      let rval = RegisterFile.find rpid rf in
      let ctrl = ControlFile.find ctrl_id cf in
      speculative_number_less_than lval rval () ctrl mem
  | SpeculativeNumberLessThanOrEqual ->
      let lpid = Operands.id_of_nth operands 0 in
      let rpid = Operands.id_of_nth operands 1 in
      let ctrl_id = Operands.id_of_nth operands 3 in
      let lval = RegisterFile.find lpid rf in
      let rval = RegisterFile.find rpid rf in
      let ctrl = ControlFile.find ctrl_id cf in
      speculative_number_less_than_or_equal lval rval () ctrl mem
  (* simplified: memory *)
  | Allocate ->
      let size_id = Operands.id_of_nth operands 0 in
      let size_value = RegisterFile.find size_id rf in
      let ct_id = Operands.id_of_nth operands 2 in
      let ct = ControlFile.find ct_id cf in
      allocate_raw size_value ct
  | AllocateRaw ->
      let size_id = Operands.id_of_nth operands 0 in
      let size_value = RegisterFile.find size_id rf in
      let ct_id = Operands.id_of_nth operands 1 in
      let ct = ControlFile.find ct_id cf in
      allocate_raw size_value ct
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
      load_element tag_value header_size repr bid ind mem
  | LoadField ->
      let base_is_tagged = Operands.const_of_nth operands 0 in
      let tag_value = tag base_is_tagged in
      let offset = Operands.const_of_nth operands 1 |> int_of_string in
      let machine_type = Operands.const_of_nth operands 2 in
      let repr = MachineType.Repr.of_rs_string machine_type in
      let bid_id = Operands.id_of_nth operands 3 in
      let bid = RegisterFile.find bid_id rf in
      load_field tag_value offset repr bid mem
  | LoadTypedElement ->
      let array_type = Operands.const_of_nth operands 0 |> int_of_string in
      let base_id = Operands.id_of_nth operands 1 in
      let base = RegisterFile.find base_id rf in
      let extern_id = Operands.id_of_nth operands 2 in
      let extern = RegisterFile.find extern_id rf in
      let ind_id = Operands.id_of_nth operands 3 in
      let ind = RegisterFile.find ind_id rf in
      load_typed_element array_type base extern ind mem
  | StoreElement ->
      let base_is_tagged = Operands.const_of_nth operands 0 in
      let tag_value = tag base_is_tagged in
      let header_size = Operands.const_of_nth operands 1 |> int_of_string in
      let machine_type = Operands.const_of_nth operands 2 in
      let repr = MachineType.Repr.of_rs_string machine_type in
      let bid_id = Operands.id_of_nth operands 3 in
      let bid = RegisterFile.find bid_id rf in
      let ind_id = Operands.id_of_nth operands 4 in
      let ind = RegisterFile.find ind_id rf in
      let value_id = Operands.id_of_nth operands 5 in
      let value = RegisterFile.find value_id rf in
      let ctrl_id = Operands.id_of_nth operands 7 in
      let ctrl = ControlFile.find ctrl_id cf in
      store_element tag_value header_size repr bid ind value mem ctrl
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
  (* simplified: type-check *)
  | NumberIsMinusZero ->
      let pid = Operands.id_of_nth operands 0 in
      let pval = RegisterFile.find pid rf in
      number_is_minus_zero pval mem
  | NumberIsNaN ->
      let pid = Operands.id_of_nth operands 0 in
      let pval = RegisterFile.find pid rf in
      number_is_nan pval mem
  | ObjectIsNaN ->
      let pid = Operands.id_of_nth operands 0 in
      let pval = RegisterFile.find pid rf in
      object_is_nan pval mem
  (* simplified: type-conversion *)
  | ChangeBitToTagged ->
      let pid = Operands.id_of_nth operands 0 in
      let pval = RegisterFile.find pid rf in
      change_bit_to_tagged pval next_bid mem
  | ChangeInt31ToTaggedSigned ->
      let pid = Operands.id_of_nth operands 0 in
      let pval = RegisterFile.find pid rf in
      change_int31_to_tagged_signed pval
  | ChangeInt32ToTagged ->
      let pid = Operands.id_of_nth operands 0 in
      let pval = RegisterFile.find pid rf in
      change_int32_to_tagged pval next_bid mem
  | ChangeInt64ToTagged ->
      let pid = Operands.id_of_nth operands 0 in
      let pval = RegisterFile.find pid rf in
      change_int64_to_tagged pval next_bid mem
  | ChangeTaggedSignedToInt64 ->
      let pid = Operands.id_of_nth operands 0 in
      let pval = RegisterFile.find pid rf in
      change_tagged_signed_to_int64 pval
  | ChangeUint32ToTagged ->
      let pid = Operands.id_of_nth operands 0 in
      let pval = RegisterFile.find pid rf in
      change_uint32_to_tagged pval next_bid mem
  | ChangeUint64ToTagged ->
      let pid = Operands.id_of_nth operands 0 in
      let pval = RegisterFile.find pid rf in
      change_uint64_to_tagged pval next_bid mem
  | CheckedFloat64ToInt32 ->
      let hint = Operands.const_of_nth operands 0 in
      let pid = Operands.id_of_nth operands 1 in
      let pval = RegisterFile.find pid rf in
      checked_float64_to_int32 hint pval
  | CheckedTaggedSignedToInt32 ->
      let pid = Operands.id_of_nth operands 0 in
      let pval = RegisterFile.find pid rf in
      checked_tagged_signed_to_int32 pval
  | CheckedTaggedToFloat64 ->
      let hint = Operands.const_of_nth operands 0 in
      let pid = Operands.id_of_nth operands 1 in
      let pval = RegisterFile.find pid rf in
      checked_tagged_to_float64 hint pval mem
  | CheckedTaggedToTaggedPointer ->
      let pid = Operands.id_of_nth operands 0 in
      let cid = Operands.id_of_nth operands 2 in
      let pval = RegisterFile.find pid rf in
      let ctrl = ControlFile.find cid cf in
      checked_tagged_to_tagged_pointer pval () ctrl
  | CheckedTaggedToTaggedSigned ->
      let pid = Operands.id_of_nth operands 0 in
      let pval = RegisterFile.find pid rf in
      checked_tagged_to_tagged_signed pval
  | CheckedTruncateTaggedToWord32 ->
      let hint = Operands.const_of_nth operands 0 in
      let pid = Operands.id_of_nth operands 1 in
      let pval = RegisterFile.find pid rf in
      checked_truncate_tagged_to_word32 hint pval mem
  | CheckedUint32ToInt32 ->
      let pid = Operands.id_of_nth operands 0 in
      let pval = RegisterFile.find pid rf in
      checked_uint32_to_int32 pval
  | NumberToBoolean ->
      let pid = Operands.id_of_nth operands 0 in
      let pval = RegisterFile.find pid rf in
      number_to_boolean pval mem
  | NumberToInt32 ->
      let pid = Operands.id_of_nth operands 0 in
      let pval = RegisterFile.find pid rf in
      number_to_int32 pval next_bid mem
  | NumberToUint32 ->
      let pid = Operands.id_of_nth operands 0 in
      let pval = RegisterFile.find pid rf in
      number_to_uint32 pval mem
  | SpeculativeToNumber ->
      let pid = Operands.id_of_nth operands 0 in
      let pval = RegisterFile.find pid rf in
      speculative_to_number pval next_bid mem
  | ToBoolean ->
      let pid = Operands.id_of_nth operands 0 in
      let pval = RegisterFile.find pid rf in
      to_boolean pval mem
  | TruncateTaggedToBit ->
      let pid = Operands.id_of_nth operands 0 in
      let pval = RegisterFile.find pid rf in
      truncate_tagged_to_bit pval mem
  (* simplified: bound-check *)
  | CheckedUint32Bounds ->
      let hint = Operands.const_of_nth operands 0 in
      let lpid = Operands.id_of_nth operands 1 in
      let rpid = Operands.id_of_nth operands 2 in
      let _eid = Operands.id_of_nth operands 3 in
      let cid = Operands.id_of_nth operands 4 in
      let lval = RegisterFile.find lpid rf in
      let rval = RegisterFile.find rpid rf in
      let ctrl = ControlFile.find cid cf in
      checked_uint32_bounds hint lval rval () ctrl
  (* machine: arithmetic *)
  | Float64Abs -> encode_machine_unary float64_abs
  | Float64Add -> encode_machine_binary float64_add
  | Float64Div -> encode_machine_binary float64_div
  | Float64ExtractHighWord32 -> encode_machine_unary float64_extract_high_word32
  | Float64Max -> encode_machine_binary float64_max
  | Float64Min -> encode_machine_binary float64_min
  | Float64Mod -> encode_machine_binary float64_mod
  | Float64Mul -> encode_machine_binary float64_mul
  | Float64Sub -> encode_machine_binary float64_sub
  | Float64RoundDown -> encode_machine_unary float64_round_down
  | Float64RoundUp -> encode_machine_unary float64_round_up
  | Float64RoundTruncate -> encode_machine_unary float64_round_truncate
  | Float64Sin -> encode_machine_unary float64_sin
  | Int32Add -> encode_machine_binary int32_add
  | Int32AddWithOverflow -> encode_machine_ovf int32_add_with_overflow
  | Int32Div ->
      let lpid = Operands.id_of_nth operands 0 in
      let rpid = Operands.id_of_nth operands 1 in
      let ctrl_id = Operands.id_of_nth operands 2 in
      let lval = RegisterFile.find lpid rf in
      let rval = RegisterFile.find rpid rf in
      let ctrl = ControlFile.find ctrl_id cf in
      int32_div lval rval ctrl
  | Int32Mul -> encode_machine_binary int32_mul
  | Int32MulWithOverflow -> encode_machine_ovf int32_mul_with_overflow
  | Int32Sub -> encode_machine_binary int32_sub
  | Int32SubWithOverflow -> encode_machine_ovf int32_sub_with_overflow
  | Int64Add -> encode_machine_binary int64_add
  | Int64Sub -> encode_machine_binary int64_sub
  | Uint32Div ->
      let lpid = Operands.id_of_nth operands 0 in
      let rpid = Operands.id_of_nth operands 1 in
      let ctrl_id = Operands.id_of_nth operands 2 in
      let lval = RegisterFile.find lpid rf in
      let rval = RegisterFile.find rpid rf in
      let ctrl = ControlFile.find ctrl_id cf in
      uint32_div lval rval ctrl
  | Word32Sar -> encode_machine_binary_with_hint word32_sar
  | Word32Shl -> encode_machine_binary word32_shl
  | Word32Shr -> encode_machine_binary word32_shr
  | Word32Xor -> encode_machine_binary word32_xor
  | Word64Sar -> encode_machine_binary_with_hint word64_sar
  | Word64Shl -> encode_machine_binary word64_shl
  | Word32ReverseBytes -> encode_machine_unary word32_reverse_bytes
  | Word64ReverseBytes -> encode_machine_unary word64_reverse_bytes
  (* machine: logic *)
  | Float64Equal -> encode_machine_binary float64_equal
  | Float64LessThan -> encode_machine_binary float64_less_than
  | Float64LessThanOrEqual -> encode_machine_binary float64_less_than_or_equal
  | Word32And -> encode_machine_binary word32_and
  | Word32Or -> encode_machine_binary word32_or
  (* machine: comparison *)
  | StackPointerGreaterThan -> stack_pointer_greater_than
  | Int32LessThan -> encode_machine_binary int32_less_than
  | Int32LessThanOrEqual -> encode_machine_binary int32_less_than_or_equal
  | Int64LessThan -> encode_machine_binary int64_less_than
  | Uint32LessThan -> encode_machine_binary uint32_less_than
  | Uint32LessThanOrEqual -> encode_machine_binary uint32_less_than_or_equal
  | Uint64LessThan -> encode_machine_binary uint64_less_than
  | Uint64LessThanOrEqual -> encode_machine_binary uint64_less_than_or_equal
  | Word32Equal -> encode_machine_binary word32_equal
  | Word64Equal -> encode_machine_binary word64_equal
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
      load ptr pos repr mem
  (* machine: bitcast *)
  | BitcastFloat32ToInt32 -> encode_machine_unary bitcast_float32_to_int32
  | BitcastFloat64ToInt64 -> encode_machine_unary bitcast_float64_to_int64
  | BitcastTaggedToWord -> encode_machine_unary bitcast_tagged_to_word
  | BitcastWord32ToWord64 -> encode_machine_unary bitcast_word32_to_word64
  | BitcastWordToTagged -> encode_machine_unary bitcast_word_to_tagged
  | TruncateFloat64ToWord32 -> encode_machine_unary truncate_float64_to_word32
  | TruncateInt64ToInt32 -> encode_machine_unary truncate_int64_to_int32
  (* machine: type-conversion *)
  | ChangeFloat64ToInt64 -> encode_machine_unary change_float64_to_int64
  | ChangeInt32ToFloat64 -> encode_machine_unary change_int32_to_float64
  | ChangeInt32ToInt64 -> encode_machine_unary change_int32_to_int64
  | ChangeInt64ToFloat64 -> encode_machine_unary change_int64_to_float64
  | ChangeUint32ToFloat64 -> encode_machine_unary change_uint32_to_float64
  | ChangeUint32ToUint64 -> encode_machine_unary change_uint32_to_uint64
  | RoundFloat64ToInt32 -> encode_machine_unary round_float64_to_int32
  | Empty -> nop
  | _ ->
      Format.printf "not implemented: %s\n" (opcode |> Opcode.to_str);
      nop

let propagate program state =
  let pc = State.pc state in
  let cf = State.control_file state in
  let uf = State.ub_file state in
  let df = State.deopt_file state in
  let _, opcode, operands = IR.instr_of pc program in
  let ub = UBFile.find (pc |> string_of_int) uf in
  let deopt = DeoptFile.find (pc |> string_of_int) df in

  (* let type_is_verified =
       match ty with Some ty -> Typer.verify value ty mem | None -> Bool.tr
     in *)
  let ub_from_input, deopt_from_input =
    match opcode with
    | End ->
        let ret_ubs = UBFile.find_all (operands |> Operands.id_of_all) uf in
        let ret_deopts =
          DeoptFile.find_all (operands |> Operands.id_of_all) df
        in
        let ret_ctrls =
          ControlFile.find_all (operands |> Operands.id_of_all) cf
        in
        ( Bool.ors
            (List.rev_map2
               (fun ctrl ub -> Bool.ands [ ctrl; ub ])
               ret_ctrls ret_ubs),
          Bool.ors
            (List.rev_map2
               (fun ctrl deopt -> Bool.ands [ ctrl; deopt ])
               ret_ctrls ret_deopts) )
    | Merge ->
        let pids = operands |> Operands.id_of_all in
        let conds = ControlFile.find_all pids cf in
        let ubs = UBFile.find_all pids uf in
        let deopts = DeoptFile.find_all pids df in
        ( Bool.ors
            (List.rev_map2 (fun cond ub -> Bool.ands [ cond; ub ]) conds ubs),
          Bool.ors
            (List.rev_map2
               (fun cond deopt -> Bool.ands [ cond; deopt ])
               conds deopts) )
    | Phi -> (
        let rev = operands |> List.rev in
        let ctrl_id = Operands.id_of_nth rev 0 in
        let ctrl_ub = UBFile.find ctrl_id uf in
        let ctrl_deopt = DeoptFile.find ctrl_id df in
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
            let incoming_deopts =
              DeoptFile.find_all
                (rev |> List.tl |> List.tl |> List.rev |> Operands.id_of_all)
                df
            in
            ( Bool.ors
                (ctrl_ub
                :: List.rev_map2
                     (fun ctrl ub -> Bool.ands [ ctrl; ub ])
                     incoming_ctrl_tokens incoming_ubs),
              Bool.ors
                (ctrl_deopt
                :: List.rev_map2
                     (fun ctrl deopt -> Bool.ands [ ctrl; deopt ])
                     incoming_ctrl_tokens incoming_deopts) )
        | Dead -> (Bool.tr, Bool.tr)
        | _ ->
            failwith
              (Format.sprintf "Phi is not implemented for incoming opcode: %s"
                 (ctrl_opcode |> Opcode.to_str)))
    | _ ->
        let pids = Operands.id_of_all operands in
        let ubs = UBFile.find_all pids uf in
        let deopts = DeoptFile.find_all pids df in
        (Bool.ors ubs, Bool.ors deopts)
  in
  let ub = Bool.ors [ ub; ub_from_input ] in
  let deopt = Bool.ors [ deopt; deopt_from_input ] in
  state |> State.update ~ub ~deopt

let rec next program state =
  let pc = State.pc state in
  let next_state = state |> encode program |> propagate program in
  if State.is_final next_state then State.finalize next_state
  else next program { next_state with pc = pc + 1 }

(* execute the program and retrieve a final state *)
let execute stage program nparams =
  (* symbols for parameters *)
  let init_state = State.init nparams stage in
  next program init_state

let check_ub_semantic nparams program =
  let state = execute "test" program nparams in
  let ub = State.ub state in
  let mem = State.memory state in
  (* params are tagged /\ not deopt *)
  let precond =
    let params = State.params state in
    let params_are_smi_or_heapnumber =
      List.mapi
        (fun bid param ->
          Bool.ors
            [
              param |> Value.has_type Type.tagged_signed;
              Bool.ands
                [
                  param |> Value.has_type Type.tagged_pointer;
                  param |> Objects.is_heap_number mem;
                  BitVec.eqi (param |> TaggedPointer.bid_of) bid;
                ];
              Bool.ors
                (List.map (Value.eq param)
                   (RegisterFile.find_all State.default_constants
                      state.register_file));
            ])
        params
      |> Bool.ands
    in
    Bool.ands [ params_are_smi_or_heapnumber; Bool.not (State.deopt state) ]
  in
  let assertion = Bool.ands [ State.assertion state; precond; ub ] in
  let status = Solver.check validator assertion in

  match status with
  | SATISFIABLE ->
      let model = Option.get (Solver.get_model validator) in
      Printf.printf "Result: Possible\n";
      Printf.printf "Example: \n";
      Printer.print_params model (State.memory state) (State.params state);
      Printer.print_counter_example program state model
  | UNSATISFIABLE -> Printf.printf "Result: Not Possible\n"
  | UNKNOWN ->
      let reason = Z3.Solver.get_reason_unknown validator in
      Printf.printf "Result: Unknown\nReason: %s" reason

let run nparams src_program tgt_program =
  let src_state = execute "before" src_program nparams in
  let tgt_state = execute "after" tgt_program nparams in

  (* params are tagged /\ not deopt *)
  let precond =
    let params = State.params src_state in
    let mem = Memory.init "mem" in
    let params_are_smi_or_heapnumber =
      List.mapi
        (fun bid param ->
          Bool.ors
            [
              param |> Value.has_type Type.tagged_signed;
              Bool.ands
                [
                  param |> Value.has_type Type.tagged_pointer;
                  param |> Objects.is_heap_number mem;
                  BitVec.eqi (param |> TaggedPointer.bid_of) bid;
                ];
              Bool.ors
                (List.map (Value.eq param)
                   (RegisterFile.find_all State.default_constants
                      src_state.register_file));
            ])
        params
      |> Bool.ands
    in
    let no_deopt =
      let src_deopt = State.deopt src_state in
      let tgt_deopt = State.deopt tgt_state in
      Bool.not (Bool.ors [ src_deopt; tgt_deopt ])
    in
    Bool.ands [ params_are_smi_or_heapnumber; no_deopt ]
  in

  let retval_is_same =
    let src_retval = State.retval src_state in
    let tgt_retval = State.retval tgt_state in
    let src_mem = State.memory src_state in
    let tgt_mem = State.memory tgt_state in
    (* assume it only returns smi or heap number pointer *)
    let to_float64 value mem =
      Bool.ite
        (value |> Value.has_type Type.tagged_pointer)
        (HeapNumber.load value mem |> HeapNumber.to_float64)
        (value |> TaggedSigned.to_float64)
    in
    Bool.eq (to_float64 src_retval src_mem) (to_float64 tgt_retval tgt_mem)
  in

  let assertion =
    Bool.ands
      [
        State.assertion src_state;
        State.assertion tgt_state;
        precond;
        Bool.not retval_is_same;
      ]
  in

  let status = Solver.check validator assertion in
  match status with
  | SATISFIABLE ->
      let model = Option.get (Solver.get_model validator) in
      Printf.printf "Result: Not Verified \n";
      Printf.printf "CounterExample: \n";
      Printer.print_params model (State.memory src_state)
        (State.params src_state);
      Printer.print_counter_example src_program src_state model;
      Printer.print_counter_example tgt_program tgt_state model
  | UNSATISFIABLE -> Printf.printf "Result: Verified\n"
  | UNKNOWN ->
      let reason = Z3.Solver.get_reason_unknown validator in
      Printf.printf "Result: Unknown\nReason: %s" reason
