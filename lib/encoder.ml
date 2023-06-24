module OpcodeSet = State.OpcodeSet
module DeoptFile = State.DeoptFile
module UBFile = State.UBFile
open ValueOperator
open Common
open Simplified
open Machine
open Z3utils

let encode_instr program ?(check_wasm = false)
    ({
       State.pc;
       control_file = cf;
       register_file = rf;
       is_angelic_value;
       is_angelic_control;
       memory = mem;
       params;
       _;
     } as state) =
  let nop state = state in
  let update_not_implemented opcode (state : State.t) =
    {
      state with
      not_implemented = true;
      not_implemented_opcodes =
        OpcodeSet.add (opcode |> Opcode.to_str) state.not_implemented_opcodes;
    }
  in

  let _, opcode, operands = IR.instr_of pc program in

  let encode_v1 op state =
    let pid = Operands.id_of_nth operands 0 in
    let pval = RegisterFile.find pid rf in
    let is_angelic_value =
      [ AngelicFile.find pid is_angelic_value ] |> Bool.ors
    in
    state |> op pval |> State.update ~is_angelic_value
  in

  let encode_v1m op state =
    let pid = Operands.id_of_nth operands 0 in
    let pval = RegisterFile.find pid rf in
    let is_angelic_value =
      [ AngelicFile.find pid is_angelic_value ] |> Bool.ors
    in
    state |> op pval mem |> State.update ~is_angelic_value
  in

  let encode_h1v1 op state =
    let hint = Operands.const_of_nth operands 0 in
    let pid = Operands.id_of_nth operands 1 in
    let pval = RegisterFile.find pid rf in
    let is_angelic_value =
      [ AngelicFile.find pid is_angelic_value ] |> Bool.ors
    in
    state |> op hint pval |> State.update ~is_angelic_value
  in

  let encode_h1v1m op state =
    let hint = Operands.const_of_nth operands 0 in
    let pid = Operands.id_of_nth operands 1 in
    let pval = RegisterFile.find pid rf in
    let is_angelic_value =
      [ AngelicFile.find pid is_angelic_value ] |> Bool.ors
    in
    state |> op hint pval mem |> State.update ~is_angelic_value
  in

  let encode_v2 op state =
    let lpid = Operands.id_of_nth operands 0 in
    let rpid = Operands.id_of_nth operands 1 in
    let lval = RegisterFile.find lpid rf in
    let rval = RegisterFile.find rpid rf in
    let is_angelic_value =
      AngelicFile.find_all [ lpid; rpid ] is_angelic_value |> Bool.ors
    in
    state |> op lval rval |> State.update ~is_angelic_value
  in

  let encode_v2m op state =
    let lpid = Operands.id_of_nth operands 0 in
    let rpid = Operands.id_of_nth operands 1 in
    let lval = RegisterFile.find lpid rf in
    let rval = RegisterFile.find rpid rf in
    let is_angelic_value =
      AngelicFile.find_all [ lpid; rpid ] is_angelic_value |> Bool.ors
    in
    state |> op lval rval mem |> State.update ~is_angelic_value
  in

  let encode_v2c1 op state =
    let lpid = Operands.id_of_nth operands 0 in
    let rpid = Operands.id_of_nth operands 1 in
    let cid = Operands.id_of_nth operands 2 in
    let lval = RegisterFile.find lpid rf in
    let rval = RegisterFile.find rpid rf in
    let ctrl = ControlFile.find cid cf in
    let is_angelic_value =
      AngelicFile.find_all [ lpid; rpid ] is_angelic_value |> Bool.ors
    in
    state |> op lval rval ctrl |> State.update ~is_angelic_value
  in

  let encode_v2c1m op state =
    let lpid = Operands.id_of_nth operands 0 in
    let rpid = Operands.id_of_nth operands 1 in
    let cid = Operands.id_of_nth operands 2 in
    let lval = RegisterFile.find lpid rf in
    let rval = RegisterFile.find rpid rf in
    let ctrl = ControlFile.find cid cf in
    let is_angelic_value =
      AngelicFile.find_all [ lpid; rpid ] is_angelic_value |> Bool.ors
    in
    state |> op lval rval ctrl mem |> State.update ~is_angelic_value
  in

  let encode_h1v2 op state =
    let hint = Operands.const_of_nth operands 0 in
    let lpid = Operands.id_of_nth operands 1 in
    let rpid = Operands.id_of_nth operands 2 in
    let lval = RegisterFile.find lpid rf in
    let rval = RegisterFile.find rpid rf in
    let is_angelic_value =
      AngelicFile.find_all [ lpid; rpid ] is_angelic_value |> Bool.ors
    in
    state |> op hint lval rval |> State.update ~is_angelic_value
  in

  let encode_h1v2e1c1 op state =
    let hint = Operands.const_of_nth operands 0 in
    let lpid = Operands.id_of_nth operands 1 in
    let rpid = Operands.id_of_nth operands 2 in
    let _eid = Operands.id_of_nth operands 3 in
    let cid = Operands.id_of_nth operands 4 in
    let lval = RegisterFile.find lpid rf in
    let rval = RegisterFile.find rpid rf in
    let ctrl = ControlFile.find cid cf in
    let is_angelic_value =
      AngelicFile.find_all [ lpid; rpid ] is_angelic_value |> Bool.ors
    in
    state |> op hint lval rval () ctrl |> State.update ~is_angelic_value
  in

  let encode_h1v2e1c1m op state =
    let hint = Operands.const_of_nth operands 0 in
    let lpid = Operands.id_of_nth operands 1 in
    let rpid = Operands.id_of_nth operands 2 in
    let _eid = Operands.id_of_nth operands 3 in
    let cid = Operands.id_of_nth operands 4 in
    let lval = RegisterFile.find lpid rf in
    let rval = RegisterFile.find rpid rf in
    let ctrl = ControlFile.find cid cf in
    let is_angelic_value =
      AngelicFile.find_all [ lpid; rpid ] is_angelic_value |> Bool.ors
    in
    state |> op hint lval rval () ctrl mem |> State.update ~is_angelic_value
  in

  let encode_v2e1c1 op state =
    let lpid = Operands.id_of_nth operands 0 in
    let rpid = Operands.id_of_nth operands 1 in
    let _eid = Operands.id_of_nth operands 2 in
    let cid = Operands.id_of_nth operands 3 in
    let lval = RegisterFile.find lpid rf in
    let rval = RegisterFile.find rpid rf in
    let ctrl = ControlFile.find cid cf in
    let is_angelic_value =
      AngelicFile.find_all [ lpid; rpid ] is_angelic_value |> Bool.ors
    in
    state |> op lval rval () ctrl |> State.update ~is_angelic_value
  in

  let encode_v3 op state =
    let fst = Operands.id_of_nth operands 0 in
    let snd = Operands.id_of_nth operands 1 in
    let lst = Operands.id_of_nth operands 2 in
    let fst_value = RegisterFile.find fst rf in
    let snd_value = RegisterFile.find snd rf in
    let lst_value = RegisterFile.find lst rf in
    let is_angelic_value =
      AngelicFile.find_all [ fst; snd; lst ] is_angelic_value |> Bool.ors
    in
    state |> op fst_value snd_value lst_value |> State.update ~is_angelic_value
  in

  let encode_v3m op state =
    let fst = Operands.id_of_nth operands 0 in
    let snd = Operands.id_of_nth operands 1 in
    let lst = Operands.id_of_nth operands 2 in
    let fst_value = RegisterFile.find fst rf in
    let snd_value = RegisterFile.find snd rf in
    let lst_value = RegisterFile.find lst rf in
    let is_angelic_value =
      AngelicFile.find_all [ fst; snd; lst ] is_angelic_value |> Bool.ors
    in
    state
    |> op fst_value snd_value lst_value mem
    |> State.update ~is_angelic_value
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
      let operand = Operands.const_of_nth operands 0 in
      let re = Re.Pcre.regexp "(0x[0-9a-f]+) <([^>]*)>" in
      let addr_name = Re.exec re operand in
      let addr =
        Re.Group.get addr_name 1 |> BitVecVal.from_istring
        |> Value.entype Type.pointer
      in
      let name = Re.Group.get addr_name 2 in
      heap_constant name addr mem
  | ExternalConstant ->
      let addr_re = Re.Pcre.regexp "(0x[0-9a-f]+)" in
      let operand = Operands.const_of_nth operands 0 in
      let c =
        Re.Group.get (Re.exec addr_re operand) 1
        |> BitVecVal.from_istring |> Value.entype Type.pointer
      in
      external_constant c
  | Int32Constant ->
      let c =
        Operands.const_of_nth operands 0
        |> BitVecVal.from_istring ~len:32
        |> BitVec.zero_extend 32
      in
      int32_constant c
  | Int64Constant ->
      let c = Operands.const_of_nth operands 0 |> BitVecVal.from_istring in
      int64_constant c
  | NumberConstant ->
      let c_str = Operands.const_of_nth operands 0 in
      number_constant c_str
  (* common: control *)
  | Projection -> (
      let idx = Operands.const_of_nth operands 0 |> int_of_string in
      let id = Operands.id_of_nth operands 1 in
      let _, ctrl_opcode, _ = IR.instr_of (id |> int_of_string) program in
      match ctrl_opcode with
      | Dead -> nop
      | _ ->
          let incoming = RegisterFile.find id rf in
          if idx >= Composed.size_of incoming then
            failwith "Projection: idx >= Composed.size_of incoming";
          projection idx incoming)
  | Branch ->
      let cond_id = Operands.id_of_nth operands 0 in
      let prev_id = Operands.id_of_nth operands 1 in
      let cond_value = RegisterFile.find cond_id rf in
      let precond_token = ControlFile.find prev_id cf in
      let is_angelic_ctrl =
        AngelicFile.find_all [ cond_id; prev_id ] is_angelic_value |> Bool.ors
      in
      branch cond_value precond_token is_angelic_ctrl
  | IfFalse ->
      let nid = Operands.id_of_nth operands 0 in
      let ctrl_token = ControlFile.find nid cf in
      let is_angelic_ctrl = AngelicFile.find nid is_angelic_control in
      if_false ctrl_token is_angelic_ctrl
  | IfTrue ->
      let nid = Operands.id_of_nth operands 0 in
      let ctrl_token = ControlFile.find nid cf in
      let is_angelic_ctrl = AngelicFile.find nid is_angelic_control in
      if_true ctrl_token is_angelic_ctrl
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
          let incoming_values =
            RegisterFile.find_all
              (rev |> List.tl |> List.rev |> Operands.id_of_all)
              rf
          in
          if List.length incoming_values <> List.length incoming_ctrl_tokens
          then
            failwith
              "Phi: number of values doesn't match with the number of controls";
          phi incoming_values incoming_ctrl_tokens
      | Dead -> nop
      | _ ->
          failwith
            (Format.sprintf "Phi is not implemented for incoming opcode: %s"
               (ctrl_opcode |> Opcode.to_str)))
  | Select -> encode_v3 select
  | Start -> start
  | Throw ->
      let nid = Operands.id_of_nth operands 0 in
      let ctrl_token = ControlFile.find nid cf in
      throw ctrl_token
  | Merge ->
      let conds = ControlFile.find_all (operands |> Operands.id_of_all) cf in
      let is_angelic_ctrl =
        List.map2 Bool.and_
          (AngelicFile.find_all
             (operands |> Operands.id_of_all)
             is_angelic_control)
          conds
        |> Bool.ands
      in
      merge conds is_angelic_ctrl
  | Unreachable ->
      let cid = Operands.id_of_nth operands 1 in
      let control = ControlFile.find cid cf in
      let control_is_angelic = AngelicFile.find cid is_angelic_control in
      unreachable control control_is_angelic
  (* common: deoptimization *)
  | Deoptimize ->
      let _frame_id = Operands.id_of_nth operands 0 in
      let _eff_id = Operands.id_of_nth operands 1 in
      let ctrl_id = Operands.id_of_nth operands 2 in
      let ctrl = ControlFile.find ctrl_id cf in
      deoptimize () () ctrl
  | DeoptimizeIf ->
      let cond_id = Operands.id_of_nth operands 0 in
      (* let frame_id = Operands.id_of_nth operands 1 in
         let eff_id = Operands.id_of_nth operands 2 in *)
      let ctrl_id = Operands.id_of_nth operands 3 in
      let deopt_cond = RegisterFile.find cond_id rf in
      let ctrl = ControlFile.find ctrl_id cf in
      let ctrl_is_angelic =
        AngelicFile.find_all [ cond_id; ctrl_id ] is_angelic_value |> Bool.ors
      in
      deoptimize_if deopt_cond () () ctrl ctrl_is_angelic
  | DeoptimizeUnless ->
      let cond_id = Operands.id_of_nth operands 0 in
      let ctrl_id = Operands.id_of_nth operands 3 in
      let cond = RegisterFile.find cond_id rf in
      let ct = ControlFile.find ctrl_id cf in
      let ctrl_is_angelic =
        AngelicFile.find_all [ cond_id; ctrl_id ] is_angelic_value |> Bool.ors
      in
      deoptimize_unless cond () () ct ctrl_is_angelic
  (* common: trap *)
  | TrapIf ->
      let cond_id = Operands.id_of_nth operands 0 in
      let ctrl_id = Operands.id_of_nth operands 1 in
      let cond = RegisterFile.find cond_id rf in
      let control = ControlFile.find ctrl_id cf in
      let control_is_angelic = AngelicFile.find ctrl_id is_angelic_control in
      trap_if cond control control_is_angelic
  | TrapUnless ->
      let hint = Operands.const_of_nth operands 0 in
      let cond_id = Operands.id_of_nth operands 1 in
      let ctrl_id = Operands.id_of_nth operands 2 in
      let cond = RegisterFile.find cond_id rf in
      let control = ControlFile.find ctrl_id cf in
      let control_is_angelic = AngelicFile.find ctrl_id is_angelic_control in
      trap_unless hint cond control control_is_angelic
  (* common: dead *)
  | Dead -> nop
  (* common: procedure *)
  | Parameter ->
      let pidx = Operands.const_of_nth operands 0 |> int_of_string in
      if 0 < pidx && pidx <= List.length params then
        let param = List.nth params (pidx - 1) in
        parameter param
      else nop
  | Call ->
      let fname = Operands.const_of_nth operands 0 in
      let args_regexp =
        Re.Pcre.regexp "[a-zA-Z0-9:_- ]*r([0-9]+)s[0-9]+i([0-9]+)f([0-9]+)"
      in
      let n_return =
        Re.Group.get (Re.exec args_regexp fname) 1 |> int_of_string
      in
      let n_input =
        try Re.Group.get (Re.exec args_regexp fname) 2 |> int_of_string
        with Not_found ->
          failwith (Printf.sprintf "Unexpected callee: %s" fname)
      in
      let n_frame =
        Re.Group.get (Re.exec args_regexp fname) 3 |> int_of_string
      in
      let params =
        List.init n_input (fun i ->
            let pid = Operands.id_of_nth operands (i + 1) in
            RegisterFile.find pid rf)
      in
      let control =
        if List.length operands = 1 + n_input + n_frame then Bool.tr
        else
          let cid = Operands.id_of_nth operands (n_input + n_frame + 1) in
          ControlFile.find cid cf
      in
      call fname n_return params control
  | Return ->
      let pid = Operands.id_of_nth operands 0 in
      let cid = Operands.id_of_nth operands 1 in
      let retval = RegisterFile.find pid rf in
      let retctrl = ControlFile.find cid cf in
      if check_wasm then return_wasm retval retctrl else return retval retctrl
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
  | JSStackCheck ->
      let _eid = Operands.id_of_nth operands 0 in
      let cid = Operands.id_of_nth operands 1 in
      let ctrl = ControlFile.find cid cf in
      js_stack_check () ctrl
  (* simplified: number-arith *)
  | CheckedInt32Add -> encode_v2e1c1 checked_int32_add
  | CheckedInt32Div -> encode_v2e1c1 checked_int32_div
  | CheckedInt32Mul -> encode_h1v2e1c1 checked_int32_mul
  | CheckedInt32Sub -> encode_v2e1c1 checked_int32_sub
  | CheckedInt64Add -> encode_v2e1c1 checked_int64_add
  | CheckedInt64Div -> encode_v2e1c1 checked_int64_div
  | CheckedInt64Mod -> encode_v2e1c1 checked_int64_mod
  | CheckedInt64Mul -> encode_v2e1c1 checked_int64_mul
  | CheckedInt64Sub -> encode_v2e1c1 checked_int64_sub
  | CheckedUint32Div -> encode_v2e1c1 checked_uint32_div
  | NumberAdd -> encode_v2m number_add
  | NumberAbs -> encode_v1m number_abs
  | NumberCeil -> encode_v1m number_ceil
  | NumberDivide -> encode_v2m number_divide
  | NumberImul -> encode_v2m number_imul
  | NumberExpm1 -> encode_v1m number_expm1
  | NumberFloor -> encode_v1m number_floor
  | NumberMax -> encode_v2m number_max
  | NumberMin -> encode_v2m number_min
  | NumberMultiply -> encode_v2m number_multiply
  | NumberModulus -> encode_v2m number_modulus
  | NumberRound -> encode_v1m number_round
  | NumberSign -> encode_v1m number_sign
  | NumberSin -> encode_v1m number_sin
  | NumberSubtract -> encode_v2m number_subtract
  | NumberTrunc -> encode_v1m number_trunc
  | SpeculativeNumberAdd -> encode_h1v2e1c1m speculative_number_add
  | SpeculativeNumberDivide -> encode_h1v2e1c1m speculative_number_divide
  | SpeculativeNumberModulus -> encode_h1v2e1c1m speculative_number_modulus
  | SpeculativeNumberMultiply -> encode_h1v2e1c1m speculative_number_multiply
  | SpeculativeNumberSubtract -> encode_h1v2e1c1m speculative_number_subtract
  | SpeculativeSafeIntegerAdd -> encode_v2c1m speculative_safe_integer_add
  | SpeculativeSafeIntegerSubtract ->
      encode_v2c1m speculative_safe_integer_subtract
  (* simplified: bitwise *)
  | BooleanNot -> encode_v1 boolean_not
  | NumberBitwiseAnd -> encode_v2m (number_bitwise "&")
  | NumberBitwiseOr -> encode_v2m (number_bitwise "|")
  | NumberBitwiseXor -> encode_v2m (number_bitwise "^")
  | NumberShiftLeft -> encode_v2m number_shift_left
  | NumberShiftRight -> encode_v2m number_shift_right
  (* simplified: comparison *)
  | NumberShiftRightLogical -> encode_v2m number_shift_right_logical
  | SpeculativeNumberBitwiseAnd ->
      encode_h1v2e1c1m (speculative_number_bitwise "&")
  | SpeculativeNumberBitwiseOr ->
      encode_h1v2e1c1m (speculative_number_bitwise "|")
  | SpeculativeNumberBitwiseXor ->
      encode_h1v2e1c1m (speculative_number_bitwise "^")
  | SpeculativeNumberShiftLeft -> encode_h1v2e1c1m speculative_number_shift_left
  | SpeculativeNumberShiftRight ->
      encode_h1v2e1c1m speculative_number_shift_right
  | SpeculativeNumberShiftRightLogical ->
      encode_h1v2e1c1m speculative_number_shift_right_logical
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
  | NumberSameValue ->
      let lpid = Operands.id_of_nth operands 0 in
      let rpid = Operands.id_of_nth operands 1 in
      let lval = RegisterFile.find lpid rf in
      let rval = RegisterFile.find rpid rf in
      number_same_value lval rval mem
  | SameValue ->
      let lpid = Operands.id_of_nth operands 0 in
      let rpid = Operands.id_of_nth operands 1 in
      let lval = RegisterFile.find lpid rf in
      let rval = RegisterFile.find rpid rf in
      same_value lval rval mem
  | ReferenceEqual ->
      let lpid = Operands.id_of_nth operands 0 in
      let rpid = Operands.id_of_nth operands 1 in
      let lval = RegisterFile.find lpid rf in
      let rval = RegisterFile.find rpid rf in
      reference_equal lval rval mem
  | SpeculativeNumberEqual -> encode_h1v2e1c1m speculative_number_equal
  | SpeculativeNumberLessThan -> encode_h1v2e1c1m speculative_number_less_than
  | SpeculativeNumberLessThanOrEqual ->
      encode_h1v2e1c1m speculative_number_less_than_or_equal
  (* simplified: bigint *)
  (* constructor *)
  | Integral32OrMinusZeroToBigInt ->
      encode_v1m integral32_or_minus_zero_to_bigint
  | SpeculativeBigIntAsIntN -> encode_h1v1m (speculative_bigint_as "int")
  | SpeculativeBigIntAsUintN -> encode_h1v1m (speculative_bigint_as "uint")
  (* arithmetic *)
  | BigIntAdd -> encode_v2m bigint_add
  | BigIntDivide -> encode_v2m bigint_divide
  | BigIntModulus -> encode_v2m bigint_modulus
  | BigIntMultiply -> encode_v2m bigint_multiply
  | BigIntSubtract -> encode_v2m bigint_subtract
  | BigIntNegate -> encode_v1m bigint_negate
  | BigIntShiftLeft -> encode_v2m bigint_shift_left
  | BigIntShiftRight -> encode_v2m bigint_shift_right
  | SpeculativeBigIntAdd -> encode_v2m speculative_bigint_add
  | SpeculativeBigIntSubtract -> encode_v2m speculative_bigint_subtract
  | SpeculativeBigIntMultiply -> encode_v2m speculative_bigint_multiply
  | SpeculativeBigIntDivide -> encode_v2m speculative_bigint_divide
  | SpeculativeBigIntModulus -> encode_v2m speculative_bigint_modulus
  | SpeculativeBigIntNegate -> encode_v1m speculative_bigint_negate
  | SpeculativeBigIntShiftLeft -> encode_v2m speculative_bigint_shift_left
  | SpeculativeBigIntShiftRight -> encode_v2m speculative_bigint_shift_right
  (* bitwise *)
  | BigIntBitwiseAnd -> encode_v2m bigint_bitwise_and
  | BigIntBitwiseOr -> encode_v2m bigint_bitwise_or
  | BigIntBitwiseXor -> encode_v2m bigint_bitwise_xor
  | SpeculativeBigIntBitwiseAnd -> encode_v2m speculative_bigint_bitwise_and
  | SpeculativeBigIntBitwiseOr -> encode_v2m speculative_bigint_bitwise_or
  | SpeculativeBigIntBitwiseXor -> encode_v2m speculative_bigint_bitwise_xor
  (* comparison *)
  | BigIntEqual -> encode_v2m bigint_equal
  | BigIntLessThan -> encode_v2m bigint_less_than
  | BigIntLessThanOrEqual -> encode_v2m bigint_less_than_or_equal
  | SpeculativeBigIntEqual -> encode_v2m speculative_bigint_equal
  | SpeculativeBigIntLessThan -> encode_v2m speculative_bigint_less_than
  | SpeculativeBigIntLessThanOrEqual ->
      encode_v2m speculative_bigint_less_than_or_equal
  (* simplified: memory *)
  | Allocate ->
      let size_id = Operands.id_of_nth operands 0 in
      let size_value = RegisterFile.find size_id rf in
      let ct_id = Operands.id_of_nth operands 2 in
      let ct = ControlFile.find ct_id cf in
      allocate_raw size_value ct mem
  | AllocateRaw ->
      let size_id = Operands.id_of_nth operands 0 in
      let size_value = RegisterFile.find size_id rf in
      let ct_id = Operands.id_of_nth operands 1 in
      let ct = ControlFile.find ct_id cf in
      allocate_raw size_value ct mem
  | LoadElement ->
      let header_size = Operands.const_of_nth operands 1 |> int_of_string in
      let machine_type = Operands.const_of_nth operands 2 in
      let repr = MachineType.Repr.of_rs_string machine_type in
      let bid_id = Operands.id_of_nth operands 3 in
      let bid = RegisterFile.find bid_id rf in
      let ind_id = Operands.id_of_nth operands 4 in
      let ind = RegisterFile.find ind_id rf in
      let cid = Operands.id_of_nth operands 5 in
      let ctrl = ControlFile.find cid cf in
      load_element header_size repr bid ind ctrl mem
  | LoadField ->
      let offset = Operands.const_of_nth operands 1 |> int_of_string in
      let machine_type = Operands.const_of_nth operands 2 in
      let repr = MachineType.Repr.of_rs_string machine_type in
      let bid_id = Operands.id_of_nth operands 3 in
      let bid = RegisterFile.find bid_id rf in
      (* let _eff_id = Operands.id_of_nth operands 4 in
         let _eff = () in *)
      let ctrl_id = Operands.id_of_nth operands 5 in
      let ctrl = ControlFile.find ctrl_id cf in
      load_field offset repr bid () ctrl mem
  | LoadFromObject ->
      let ptr_id = Operands.id_of_nth operands 0 in
      let ptr = RegisterFile.find ptr_id rf in
      let pos_id = Operands.id_of_nth operands 1 in
      let pos = RegisterFile.find pos_id rf in
      let repr = Operands.const_of_nth operands 2 |> Repr.of_rs_string in
      let cid = Operands.id_of_nth operands 3 in
      let ctrl = ControlFile.find cid cf in
      load ptr pos repr ctrl mem
  | LoadTypedElement ->
      let array_type = Operands.const_of_nth operands 0 |> int_of_string in
      let base_id = Operands.id_of_nth operands 1 in
      let base = RegisterFile.find base_id rf in
      let extern_id = Operands.id_of_nth operands 2 in
      let extern = RegisterFile.find extern_id rf in
      let ind_id = Operands.id_of_nth operands 3 in
      let ind = RegisterFile.find ind_id rf in
      let cid = Operands.id_of_nth operands 4 in
      let ctrl = ControlFile.find cid cf in
      load_typed_element array_type base extern ind ctrl mem
  | StoreElement ->
      let header_size = Operands.const_of_nth operands 1 |> int_of_string in
      let machine_type = Operands.const_of_nth operands 2 in
      let repr = MachineType.Repr.of_rs_string machine_type in
      let bid_id = Operands.id_of_nth operands 3 in
      let bid = RegisterFile.find bid_id rf in
      let ind_id = Operands.id_of_nth operands 4 in
      let ind = RegisterFile.find ind_id rf in
      let value_id = Operands.id_of_nth operands 5 in
      let value = RegisterFile.find value_id rf in
      (* let _eff_id = Operands.id_of_nth operands 6 in
         let _eff = () in *)
      let ctrl_id = Operands.id_of_nth operands 7 in
      let ctrl = ControlFile.find ctrl_id cf in
      store_element header_size repr bid ind value mem ctrl
  | StoreField ->
      let ptr_id = Operands.id_of_nth operands 0 in
      let ptr = RegisterFile.find ptr_id rf in
      let offset = Operands.const_of_nth operands 1 |> int_of_string in
      let machine_type = Operands.const_of_nth operands 2 in
      let repr = MachineType.Repr.of_rs_string machine_type in
      let value_id = Operands.id_of_nth operands 3 in
      let value = RegisterFile.find value_id rf in
      (* let _eff_id = Operands.id_of_nth operands 4 in
         let _eff = () in *)
      let ctrl_id = Operands.id_of_nth operands 5 in
      let ctrl = ControlFile.find ctrl_id cf in
      store_field ptr offset repr value () ctrl mem
  (* simplified: string*)
  (* arithmetic *)
  | StringLength -> encode_v1m string_length
  | StringCharCodeAt -> encode_v2m string_char_code_at
  | StringCodePointAt -> encode_v2m string_code_point_at
  | StringFromSingleCharCode -> encode_v1m string_from_single_char_code
  | StringFromSingleCodePoint -> encode_v1m string_from_single_code_point
  | StringIndexOf -> encode_v3m string_index_of
  | StringConcat -> encode_v3m string_concat
  | StringEqual -> encode_v2m string_equal
  | StringLessThan -> encode_v2m string_less_than
  | StringLessThanOrEqual -> encode_v2m string_less_than_or_equal
  | StringSubstring -> encode_v3m string_sub_string
  | StringToNumber -> encode_v1m string_to_number
  (* simplified: type-check *)
  | CheckBigInt ->
      let value_id = Operands.id_of_nth operands 0 in
      let value = RegisterFile.find value_id rf in
      let ctrl_id = Operands.id_of_nth operands 2 in
      let ctrl = ControlFile.find ctrl_id cf in
      check_big_int value ctrl mem
  | CheckString ->
      let value_id = Operands.id_of_nth operands 0 in
      let value = RegisterFile.find value_id rf in
      let ctrl_id = Operands.id_of_nth operands 2 in
      let ctrl = ControlFile.find ctrl_id cf in
      check_string value ctrl mem
  | NumberIsInteger ->
      let pid = Operands.id_of_nth operands 0 in
      let value = RegisterFile.find pid rf in
      number_is_integer value mem
  | NumberIsMinusZero ->
      let pid = Operands.id_of_nth operands 0 in
      let pval = RegisterFile.find pid rf in
      number_is_minus_zero pval mem
  | NumberIsNaN ->
      let pid = Operands.id_of_nth operands 0 in
      let pval = RegisterFile.find pid rf in
      number_is_nan pval mem
  | NumberIsSafeInteger ->
      let pid = Operands.id_of_nth operands 0 in
      let pval = RegisterFile.find pid rf in
      number_is_safe_integer pval mem
  | ObjectIsMinusZero ->
      let pid = Operands.id_of_nth operands 0 in
      let pval = RegisterFile.find pid rf in
      object_is_minus_zero pval mem
  | ObjectIsNaN ->
      let pid = Operands.id_of_nth operands 0 in
      let pval = RegisterFile.find pid rf in
      object_is_nan pval mem
  | ObjectIsSmi ->
      let pid = Operands.id_of_nth operands 0 in
      let pval = RegisterFile.find pid rf in
      object_is_smi pval
      (* simplified: type-conversion *)
  | ChangeBitToTagged ->
      let pid = Operands.id_of_nth operands 0 in
      let pval = RegisterFile.find pid rf in
      change_bit_to_tagged pval
  | ChangeFloat64ToTagged ->
      let mode = Operands.const_of_nth operands 0 in
      let pid = Operands.id_of_nth operands 1 in
      let pval = RegisterFile.find pid rf in
      change_float64_to_tagged mode pval mem
  | ChangeInt31ToTaggedSigned ->
      let pid = Operands.id_of_nth operands 0 in
      let pval = RegisterFile.find pid rf in
      change_int31_to_tagged_signed pval
  | ChangeInt32ToTagged ->
      let pid = Operands.id_of_nth operands 0 in
      let pval = RegisterFile.find pid rf in
      change_int32_to_tagged pval
  | ChangeInt64ToBigInt ->
      let value_id = Operands.id_of_nth operands 0 in
      let value = RegisterFile.find value_id rf in
      change_int64_to_bigint value mem
  | ChangeInt64ToTagged ->
      let pid = Operands.id_of_nth operands 0 in
      let pval = RegisterFile.find pid rf in
      change_int64_to_tagged pval
  | ChangeTaggedToBit -> encode_v1 change_tagged_to_bit
  | ChangeTaggedToFloat64 -> encode_v1 change_tagged_to_float64
  | ChangeTaggedSignedToInt32 -> encode_v1 change_tagged_signed_to_int32
  | ChangeTaggedSignedToInt64 -> encode_v1 change_tagged_signed_to_int64
  | ChangeUint32ToTagged ->
      let pid = Operands.id_of_nth operands 0 in
      let pval = RegisterFile.find pid rf in
      change_uint32_to_tagged pval
  | ChangeUint64ToBigInt ->
      let value_id = Operands.id_of_nth operands 0 in
      let value = RegisterFile.find value_id rf in
      change_uint64_to_bigint value mem
  | ChangeUint64ToTagged ->
      let pid = Operands.id_of_nth operands 0 in
      let pval = RegisterFile.find pid rf in
      change_uint64_to_tagged pval
  | CheckedBigIntToBigInt64 ->
      let value_id = Operands.id_of_nth operands 0 in
      let value = RegisterFile.find value_id rf in
      let ctrl_id = Operands.id_of_nth operands 2 in
      let ctrl = ControlFile.find ctrl_id cf in
      checked_bigint_to_bigint64 value ctrl mem
  | CheckedFloat64ToInt32 -> encode_h1v1 checked_float64_to_int32
  | CheckedTaggedSignedToInt32 -> encode_v1 checked_tagged_signed_to_int32
  | CheckedTaggedToFloat64 -> encode_h1v1m checked_tagged_to_float64
  | CheckedTaggedToInt64 -> encode_h1v1m checked_tagged_to_int64
  | CheckedTaggedToTaggedPointer ->
      let pid = Operands.id_of_nth operands 0 in
      let _eid = Operands.id_of_nth operands 1 in
      let cid = Operands.id_of_nth operands 2 in
      let pval = RegisterFile.find pid rf in
      let ctrl = ControlFile.find cid cf in
      checked_tagged_to_tagged_pointer pval () ctrl
  | CheckedTaggedToTaggedSigned ->
      let pid = Operands.id_of_nth operands 0 in
      let _eid = Operands.id_of_nth operands 1 in
      let cid = Operands.id_of_nth operands 2 in
      let pval = RegisterFile.find pid rf in
      let ctrl = ControlFile.find cid cf in
      checked_tagged_to_tagged_signed pval () ctrl
  | CheckedTruncateTaggedToWord32 ->
      let hint = Operands.const_of_nth operands 0 in
      let pid = Operands.id_of_nth operands 1 in
      let pval = RegisterFile.find pid rf in
      checked_truncate_tagged_to_word32 hint pval mem
  | CheckedUint32ToInt32 -> encode_v1 checked_uint32_to_int32
  | CheckedUint64ToInt64 -> encode_v1 checked_uint64_to_int64
  | NumberToBoolean ->
      let pid = Operands.id_of_nth operands 0 in
      let pval = RegisterFile.find pid rf in
      number_to_boolean pval mem
  | NumberToInt32 ->
      let pid = Operands.id_of_nth operands 0 in
      let pval = RegisterFile.find pid rf in
      number_to_int32 pval mem
  | NumberToString ->
      let pid = Operands.id_of_nth operands 0 in
      let pval = RegisterFile.find pid rf in
      number_to_string pval mem
  | NumberToUint32 ->
      let pid = Operands.id_of_nth operands 0 in
      let pval = RegisterFile.find pid rf in
      number_to_uint32 pval mem
  | SpeculativeToNumber ->
      let pid = Operands.id_of_nth operands 0 in
      let _eid = Operands.id_of_nth operands 1 in
      let cid = Operands.id_of_nth operands 2 in
      let pval = RegisterFile.find pid rf in
      let ctrl = ControlFile.find cid cf in
      speculative_to_number pval () ctrl mem
  | ToBoolean ->
      let pid = Operands.id_of_nth operands 0 in
      let pval = RegisterFile.find pid rf in
      to_boolean pval mem
  | TruncateBigIntToWord64 ->
      let value_id = Operands.id_of_nth operands 0 in
      let value = RegisterFile.find value_id rf in
      truncate_big_int_to_word64 value mem
  | TruncateTaggedToBit ->
      let pid = Operands.id_of_nth operands 0 in
      let pval = RegisterFile.find pid rf in
      truncate_tagged_to_bit pval mem
  | TruncateTaggedPointerToBit ->
      let pid = Operands.id_of_nth operands 0 in
      let pval = RegisterFile.find pid rf in
      truncate_tagged_pointer_to_bit pval mem
  | TruncateTaggedToWord32 ->
      let pid = Operands.id_of_nth operands 0 in
      let pval = RegisterFile.find pid rf in
      truncate_tagged_to_word32 pval
  (* simplified: bound-check *)
  | CheckIf ->
      let pid = Operands.id_of_nth operands 0 in
      let _eff = Operands.id_of_nth operands 1 in
      let cid = Operands.id_of_nth operands 2 in
      let pval = RegisterFile.find pid rf in
      let ctrl = ControlFile.find cid cf in
      check_if pval () ctrl
  | CheckMaps -> nop
  | CheckBounds -> encode_h1v2e1c1m check_bounds
  | CheckedUint32Bounds -> encode_h1v2e1c1 checked_uint32_bounds
  | CheckedUint64Bounds -> encode_h1v2e1c1 checked_uint64_bounds
  | EnsureWritableFastElements ->
      let rpid = Operands.id_of_nth operands 1 in
      let _eid = Operands.id_of_nth operands 2 in
      let cid = Operands.id_of_nth operands 3 in
      let rval = RegisterFile.find rpid rf in
      let ctrl = ControlFile.find cid cf in
      ensure_writable_fast_elements () rval () ctrl
  (* machine: arithmetic *)
  | Float32Abs -> encode_v1 float32_abs
  | Float32Add -> encode_v2 float32_add
  | Float32Div -> encode_v2 float32_div
  | Float32Max -> encode_v2 float32_max
  | Float32Min -> encode_v2 float32_min
  | Float32Mul -> encode_v2 float32_mul
  | Float32Neg -> encode_v1 float32_neg
  | Float64Abs -> encode_v1 float64_abs
  | Float64Add -> encode_v2 float64_add
  | Float64Asin -> encode_v1 float64_asin
  | Float64Asinh -> encode_v1 float64_asinh
  | Float64Div -> encode_v2 float64_div
  | Float64ExtractHighWord32 -> encode_v1 float64_extract_high_word32
  | Float64Max -> encode_v2 float64_max
  | Float64Min -> encode_v2 float64_min
  | Float64Mod -> encode_v2 float64_mod
  | Float64Mul -> encode_v2 float64_mul
  | Float64Neg -> encode_v1 float64_neg
  | Float64SilenceNaN -> encode_v1 float64_silence_nan
  | Float64Sub -> encode_v2 float64_sub
  | Float64RoundDown -> encode_v1 float64_round_down
  | Float64RoundUp -> encode_v1 float64_round_up
  | Float64RoundTruncate -> encode_v1 float64_round_truncate
  | Float64RoundTiesAway -> encode_v1 float64_round_ties_away
  | Float64RoundTiesEven -> encode_v1 float64_round_ties_even
  | Float64Sin -> encode_v1 float64_sin
  | Int32Add -> encode_v2 int32_add
  | Int32AddWithOverflow -> encode_v2c1 int32_add_with_overflow
  | Int32Div -> encode_v2c1 int32_div
  | Int32Mod -> encode_v2c1 int32_mod
  | Int32Mul -> encode_v2 int32_mul
  | Int32MulWithOverflow -> encode_v2c1 int32_mul_with_overflow
  | Int32Sub -> encode_v2 int32_sub
  | Int32SubWithOverflow -> encode_v2c1 int32_sub_with_overflow
  | Int64Add -> encode_v2 int64_add
  | Int64AddWithOverflow -> encode_v2c1 int64_add_with_overflow
  | Int64Mul -> encode_v2 int64_mul
  | Int64MulWithOverflow -> encode_v2c1 int64_mul_with_overflow
  | Int64Sub -> encode_v2 int64_sub
  | Int64SubWithOverflow -> encode_v2c1 int64_sub_with_overflow
  | Int64Div -> encode_v2c1 int64_div
  | Int64Mod -> encode_v2c1 int64_mod
  | Uint32Div -> encode_v2c1 uint32_div
  | Uint32Mod -> encode_v2c1 uint32_mod
  | Word32And -> encode_v2 word32_and
  | Word32Or -> encode_v2 word32_or
  | Word32Rol -> encode_v2 word32_rol
  | Word32Ror -> encode_v2 word32_ror
  | Word32Sar -> encode_h1v2 word32_sar
  | Word32Shl -> encode_v2 word32_shl
  | Word32Shr -> encode_v2 word32_shr
  | Word32Xor -> encode_v2 word32_xor
  | Word64And -> encode_v2 word64_and
  | Word64Or -> encode_v2 word64_or
  | Word64Rol -> encode_v2 word64_rol
  | Word64Ror -> encode_v2 word64_ror
  | Word64Sar -> encode_h1v2 word64_sar
  | Word64Shl -> encode_v2 word64_shl
  | Word64Shr -> encode_v2 word64_shr
  | Word64Xor -> encode_v2 word64_xor
  | Word32ReverseBytes -> encode_v1 word32_reverse_bytes
  | Word64ReverseBytes -> encode_v1 word64_reverse_bytes
  (* machine: logic *)
  | Float32Equal -> encode_v2 float32_equal
  | Float32LessThan -> encode_v2 float32_less_than
  | Float32LessThanOrEqual -> encode_v2 float32_less_than_or_equal
  | Float64Equal -> encode_v2 float64_equal
  | Float64LessThan -> encode_v2 float64_less_than
  | Float64LessThanOrEqual -> encode_v2 float64_less_than_or_equal
  (* machine: comparison *)
  | StackPointerGreaterThan -> stack_pointer_greater_than
  | Int32LessThan -> encode_v2 int32_less_than
  | Int32LessThanOrEqual -> encode_v2 int32_less_than_or_equal
  | Int64LessThan -> encode_v2 int64_less_than
  | Int64LessThanOrEqual -> encode_v2 int64_less_than_or_equal
  | Uint32LessThan -> encode_v2 uint32_less_than
  | Uint32LessThanOrEqual -> encode_v2 uint32_less_than_or_equal
  | Uint64LessThan -> encode_v2 uint64_less_than
  | Uint64LessThanOrEqual -> encode_v2 uint64_less_than_or_equal
  | Word32Equal -> encode_v2 word32_equal
  | Word64Equal -> encode_v2 word64_equal
  (* machine: memory *)
  | Load | ProtectedLoad ->
      let ptr_id = Operands.id_of_nth operands 0 in
      let ptr = RegisterFile.find ptr_id rf in
      let pos_id = Operands.id_of_nth operands 1 in
      let pos = RegisterFile.find pos_id rf in
      let repr = Operands.const_of_nth operands 2 |> Repr.of_rs_string in
      let cid = Operands.id_of_nth operands 3 in
      let ctrl = ControlFile.find cid cf in
      load ptr pos repr ctrl mem
  | LoadImmutable ->
      let ptr_id = Operands.id_of_nth operands 0 in
      let ptr = RegisterFile.find ptr_id rf in
      let pos_id = Operands.id_of_nth operands 1 in
      let pos = RegisterFile.find pos_id rf in
      let repr = Operands.const_of_nth operands 2 |> Repr.of_rs_string in
      load ptr pos repr Bool.tr mem
  | Store | ProtectedStore ->
      let ptr_id = Operands.id_of_nth operands 0 in
      let ptr = RegisterFile.find ptr_id rf in
      let pos_id = Operands.id_of_nth operands 1 in
      let pos = RegisterFile.find pos_id rf in
      let repr = Operands.const_of_nth operands 2 |> Repr.of_string in
      let value_id = Operands.id_of_nth operands 3 in
      let value = RegisterFile.find value_id rf in
      let cid = Operands.id_of_nth operands 3 in
      let ctrl = ControlFile.find cid cf in
      store ptr pos repr value ctrl mem
  (* machine: bitcast *)
  | BitcastFloat32ToInt32 -> encode_v1 bitcast_float32_to_int32
  | BitcastFloat64ToInt64 -> encode_v1 bitcast_float64_to_int64
  | BitcastInt64ToFloat64 -> encode_v1 bitcast_int64_to_float64
  | BitcastTaggedToWord -> encode_v1 bitcast_tagged_to_word
  | BitcastWord32ToWord64 -> encode_v1 bitcast_word32_to_word64
  | BitcastWordToTagged -> encode_v1 bitcast_word_to_tagged
  | TruncateFloat64ToInt64 -> encode_v1 truncate_float64_to_int64
  | TruncateFloat64ToWord32 -> encode_v1 truncate_float64_to_word32
  | TruncateInt64ToInt32 -> encode_v1 truncate_int64_to_int32
  (* machine: type-conversion *)
  | ChangeFloat64ToInt32 -> encode_v1 change_float64_to_int32
  | ChangeFloat64ToInt64 -> encode_v1 change_float64_to_int64
  | ChangeFloat64ToUint32 -> encode_v1 change_float64_to_uint32
  | ChangeFloat64ToUint64 -> encode_v1 change_float64_to_uint64
  | ChangeInt32ToFloat64 -> encode_v1 change_int32_to_float64
  | ChangeInt32ToInt64 -> encode_v1 change_int32_to_int64
  | ChangeInt64ToFloat64 -> encode_v1 change_int64_to_float64
  | ChangeUint32ToFloat64 -> encode_v1 change_uint32_to_float64
  | ChangeUint32ToUint64 -> encode_v1 change_uint32_to_uint64
  | SignExtendWord16ToInt32 -> encode_v1 sign_extend_word16_to_int32
  | SignExtendWord16ToInt64 -> encode_v1 sign_extend_word16_to_int64
  | SignExtendWord32ToInt64 -> encode_v1 sign_extend_word32_to_int64
  | SignExtendWord8ToInt32 -> encode_v1 sign_extend_word8_to_int32
  | SignExtendWord8ToInt64 -> encode_v1 sign_extend_word8_to_int64
  | RoundFloat64ToInt32 -> encode_v1 round_float64_to_int32
  | Empty -> nop
  | BeginRegion | StateValues | Checkpoint | EffectPhi | TypedStateValues
  | ObjectId | FrameState | TypedObjectState | LoadStackCheckOffset ->
      nop
  | _ -> update_not_implemented opcode

let propagate program (state : State.t) =
  let pc = State.pc state in
  let ({
         control_file = cf;
         ub_file = uf;
         register_file = rf;
         deopt_file = df;
         is_angelic_value = af;
         memory = mem;
         _;
       }
        : State.t) =
    state
  in
  let ty, opcode, operands = IR.instr_of pc program in
  let ub = UBFile.find (pc |> string_of_int) uf in
  let deopt = DeoptFile.find (pc |> string_of_int) df in

  let type_assertion, type_is_verified =
    let is_angelic_value = AngelicFile.find (pc |> string_of_int) af in
    let ty_check =
      let value = RegisterFile.find (pc |> string_of_int) rf in
      match ty with
      | Some ty ->
          if String.starts_with ~prefix:"Word" (Opcode.to_str opcode) then
            let flipped = Value.flip_type value in
            [ value; flipped ]
            |> List.map (fun v -> Typer.verify v ty mem)
            |> Bool.ors
          else Typer.verify value ty mem
      | None -> Bool.tr
    in
    (Bool.implies is_angelic_value ty_check, ty_check)
  in
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
                (rev |> List.tl |> List.rev |> Operands.id_of_all)
                uf
            in
            let incoming_deopts =
              DeoptFile.find_all
                (rev |> List.tl |> List.rev |> Operands.id_of_all)
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
  let ub =
    if state.check_type then
      Bool.ors [ ub; Bool.not type_is_verified; ub_from_input ]
    else Bool.ors [ ub; ub_from_input ]
  in
  let deopt = Bool.ors [ deopt; deopt_from_input ] in
  let state =
    if state.check_type then
      {
        state with
        assertion = Bool.ands [ state.State.assertion; type_assertion ];
      }
    else state
  in
  state |> State.update ~ub ~deopt

(* encode the program and retrieve a final state *)
let encode_pgr stage program ?(check_type = false) ?(check_wasm = false) nparams
    =
  let init_state = State.init nparams ~check_type stage in
  let rec next program state =
    let pc = State.pc state in
    let next_state =
      state |> encode_instr ~check_wasm program |> propagate program
    in
    if State.is_final next_state then
      next_state |> Assertion.set_assertion program |> State.finalize
    else next program { next_state with pc = pc + 1 }
  in
  next program init_state