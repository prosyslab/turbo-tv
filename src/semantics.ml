open Err
open Z3utils

module Params = struct
  module Param = struct
    type t = BitVec.t

    (* paramater id *)
    let init pid = BitVec.init pid
  end

  type t = Param.t list

  let init nparams =
    let rec mk_param cnt params =
      if cnt == nparams then params
      else
        mk_param (cnt + 1) (Param.init ("p" ^ (cnt |> string_of_int)) :: params)
    in
    mk_param 0 []
end

module Value = struct
  type id = string
  type t = BitVec.t

  let empty = BitVecVal.zero 1 ()
  let to_str t = str_of_exp t

  (* constants *)
  let tylen = 5
  let datalen = 64
  let len = tylen + datalen
  let smilen = 31
  let smimask = 0xfffffffe
  let smimin = -1073741824
  let smimax = 1073741823

  (* type-constants *)
  let int8_ty = BitVecVal.of_int ~len:tylen 0
  let uint8_ty = BitVecVal.of_int ~len:tylen 1
  let int16_ty = BitVecVal.of_int ~len:tylen 2
  let uint16_ty = BitVecVal.of_int ~len:tylen 3
  let int32_ty = BitVecVal.of_int ~len:tylen 4
  let uint32_ty = BitVecVal.of_int ~len:tylen 5
  let int64_ty = BitVecVal.of_int ~len:tylen 6
  let uint64_ty = BitVecVal.of_int ~len:tylen 7
  let float32_ty = BitVecVal.of_int ~len:tylen 8
  let float64_ty = BitVecVal.of_int ~len:tylen 9
  let simd128_ty = BitVecVal.of_int ~len:tylen 10
  let pointer_ty = BitVecVal.of_int ~len:tylen 11
  let tagged_pointer_ty = BitVecVal.of_int ~len:tylen 12
  let map_in_header_ty = BitVecVal.of_int ~len:tylen 13
  let tagged_signed_ty = BitVecVal.of_int ~len:tylen 14
  let any_tagged_ty = BitVecVal.of_int ~len:tylen 15
  let compressed_pointer_ty = BitVecVal.of_int ~len:tylen 16
  let any_compressed_ty = BitVecVal.of_int ~len:tylen 17
  let sandboxed_pointer_ty = BitVecVal.of_int ~len:tylen 18
  let bool_ty = BitVecVal.of_int ~len:tylen 19
  let none_ty = BitVecVal.of_int ~len:tylen 20

  (* getter *)
  let ty_of t = BitVec.extract 0 tylen t
  let data_of t = BitVec.extract tylen len t

  (* typing *)
  let data_to_int32 data = BitVec.concat int32_ty data
  let data_to_int64 data = BitVec.concat int64_ty data
  let data_to_float64 data = BitVec.concat float64_ty data
  let data_to_pointer data = BitVec.concat pointer_ty data
  let data_to_tagged_signed data = BitVec.concat tagged_signed_ty data
  let data_to_any_tagged data = BitVec.concat any_tagged_ty data

  (* type check *)
  let is_int32 value =
    let value_ty = ty_of value in
    BitVec.eqb value_ty int32_ty

  let is_int64 value =
    let value_ty = ty_of value in
    BitVec.eqb value_ty int64_ty

  let is_pointer value =
    let value_ty = ty_of value in
    BitVec.eqb value_ty pointer_ty

  let is_tagged_signed value =
    let value_ty = ty_of value in
    BitVec.eqb value_ty tagged_signed_ty

  (* comparison *)
  (* lty = rty && ldata = rdata *)
  let is_equal lval rval = BitVec.eqb lval rval

  (* ldata = rdata *)
  let is_weak_equal lval rval =
    let ldata = data_of lval in
    let rdata = data_of rval in
    BitVec.eqb ldata rdata

  let can_be_smi bv = Bool.ands [ BitVec.sgei bv smimin; BitVec.slti bv smimax ]

  (* common: constants *)
  let int32_constant vid c =
    let value = BitVec.init ~len vid in
    let cval = BitVec.concat int32_ty (BitVecVal.of_str c) in
    let assertion = Bool.ands [ is_equal value cval ] in
    (value, assertion)

  let int64_constant vid c =
    let value = BitVec.init ~len vid in
    let cval = BitVec.concat int64_ty (BitVecVal.of_str c) in
    let assertion = Bool.ands [ is_equal value cval ] in
    (value, assertion)

  let external_constant vid c =
    let value = BitVec.init ~len vid in
    let cval = BitVec.concat pointer_ty (BitVecVal.of_str c) in
    let assertion = Bool.ands [ is_equal value cval ] in
    (value, assertion)

  let heap_constant = external_constant

  let number_constant vid c =
    let value = BitVec.init ~len vid in
    let cbv = BitVecVal.of_str c in

    value |> to_str |> print_endline;
    data_to_tagged_signed cbv |> to_str |> print_endline;

    let c_is_smi =
      Bool.ands [ can_be_smi cbv; is_equal value (data_to_tagged_signed cbv) ]
    in

    let c_is_not_smi =
      Bool.ands
        [ Bool.not (can_be_smi cbv); is_equal value (data_to_any_tagged cbv) ]
    in

    let assertion = Bool.ands [ c_is_smi; c_is_not_smi ] in
    (value, assertion)

  (* simplified: arithmetic *)
  let speculative_safe_integer_add vid lval rval =
    let value = BitVec.init ~len vid in
    let ldata = data_of lval in
    let rdata = data_of rval in
    let res =
      BitVec.andi (BitVec.addb ldata rdata) smimask |> data_to_tagged_signed
    in

    let assertion =
      Bool.ands
        [ is_tagged_signed lval; is_tagged_signed rval; is_equal value res ]
    in

    (value, assertion)

  (* simplified: type-conversion *)
  let change_int32_to_tagged vid pval =
    let value = BitVec.init ~len vid in
    let pdata = data_of pval in
    let assertion =
      Bool.ands [ is_int32 pval; is_equal value (data_to_tagged_signed pdata) ]
    in

    (value, assertion)

  let change_int32_to_float64 vid pval =
    let value = BitVec.init ~len vid in
    let pdata = data_of pval in
    let ovf = BitVec.ugei (BitVec.addb pdata pdata) smimax in

    (* TODO: memory allocation *)
    (* let if_ovf = Bool.ands [ ovf ] in *)
    let if_not_ovf =
      Bool.ands [ Bool.not ovf; is_equal value (data_to_tagged_signed pdata) ]
    in

    (* TODO: memory allocation *)
    (* let assertion = Bool.ands [ if_ovf; if_not_ovf ] in *)
    let assertion = Bool.ands [ if_not_ovf ] in
    (value, assertion)

  let checked_tagged_signed_to_int32 vid pval =
    let value = BitVec.init ~len vid in
    let pdata = data_of pval in

    (* TODO: handling deoptimization *)
    (* let deopt = Bool.not (is_tagged_signed pval) in *)
    let assertion =
      Bool.ands [ is_tagged_signed pval; is_equal value (data_to_int32 pdata) ]
    in

    (value, assertion)

  (* machine: arithmetic *)
  (* value = (lval + rval) mod 2^32 *)
  let int32add vid lval rval =
    let value = BitVec.init ~len vid in
    let ldata = data_of lval in
    let rdata = data_of rval in
    let res = BitVec.andi (BitVec.addb ldata rdata) smimask |> data_to_int32 in

    let assertion =
      Bool.ands [ is_int32 lval; is_int32 rval; is_equal value res ]
    in

    (value, assertion)

  let parameter _vid _param = failwith "Not implemented"
  let return _vid _pval = failwith "Not implemented"
end

module RegisterFile = struct
  module R = Map.Make (String)

  let add = R.add

  let find vid rf =
    try R.find vid rf
    with Not_found ->
      let cause = vid in
      let reason = Format.sprintf "Cannot find %s from RegisterFile" cause in
      err (IdNotFound (cause, reason))

  let empty = R.empty
  let iter = R.iter
  let print _t = failwith "Not implemented"
end

module State = struct
  type t = {
    pc : IR.Node.id;
    register_file : Value.t RegisterFile.R.t;
    params : BitVec.t list;
    retvar : BitVec.t Option.t;
    assertion : BitVec.t;
  }

  let init nparams : t =
    {
      pc = 0;
      register_file = RegisterFile.empty;
      params = Params.init nparams;
      retvar = None;
      assertion = Bool.tr;
    }

  let update pc register_file assertion t =
    { t with pc; register_file; assertion }

  (* getter *)
  let pc t = t.pc
  let register_file t = t.register_file
  let params t = t.params
  let retvar t = t.retvar
  let assertion t = t.assertion
  let is_final t = t.pc = -1
end

(* apply semantics to create SMT query *)
let apply program state prefix =
  let pc = State.pc state in
  let rf = State.register_file state in
  let params = State.params state in
  let vid = prefix ^ string_of_int pc in

  let opcode, operands = IR.instr_of pc program in
  let next_pc = match opcode with Return -> -1 | _ -> pc + 1 in

  let value, assertion =
    match opcode with
    (* common: constants *)
    | HeapConstant | ExternalConstant ->
        Operands.const_of_nth operands 0 |> Value.heap_constant vid
    | Int32Constant ->
        Operands.const_of_nth operands 0 |> Value.int32_constant vid
    | Int64Constant ->
        Operands.const_of_nth operands 0 |> Value.int64_constant vid
    | NumberConstant ->
        Operands.const_of_nth operands 0 |> Value.number_constant vid
    (* common: control *)
    | Branch | Projection -> failwith "Not implemented"
    (* common: procedure *)
    | Parameter ->
        let pidx = Operands.const_of_nth operands 0 |> int_of_string in
        if 0 < pidx && pidx <= List.length params then
          let param = List.nth params (pidx - 1) in
          Value.parameter vid param
        else (Value.empty, Bool.tr)
    | Return | Call | End -> failwith "Not implemented"
    (* simplified: arithmetic *)
    | SpeculativeSafeIntegerAdd ->
        let lpid = prefix ^ Operands.id_of_nth operands 0 in
        let rpid = prefix ^ Operands.id_of_nth operands 1 in
        let lval = RegisterFile.find lpid rf in
        let rval = RegisterFile.find rpid rf in
        Value.speculative_safe_integer_add vid lval rval
    (* simplified: memory *)
    | AllocateRaw | StoreField -> failwith "Not implemented"
    (* simplified: type-conversion *)
    | ChangeInt32ToTagged ->
        let pid = prefix ^ Operands.id_of_nth operands 0 in
        let pval = RegisterFile.find pid rf in
        Value.change_int32_to_tagged vid pval
    | ChangeInt32ToFloat64 ->
        let pid = prefix ^ Operands.id_of_nth operands 0 in
        let pval = RegisterFile.find pid rf in
        Value.change_int32_to_float64 vid pval
    | CheckedTaggedSignedToInt32 ->
        let pid = prefix ^ Operands.id_of_nth operands 0 in
        let pval = RegisterFile.find pid rf in
        Value.checked_tagged_signed_to_int32 vid pval
    (* machine: arithmetic *)
    | Int32Add ->
        let lpid = prefix ^ Operands.id_of_nth operands 0 in
        let rpid = prefix ^ Operands.id_of_nth operands 1 in
        let lval = RegisterFile.find lpid rf in
        let rval = RegisterFile.find rpid rf in
        Value.int32add vid lval rval
    | Int32AddWithOverflow | Int64Add | Int64Sub | Word32Sar
    (* machine: comparison *)
    | StackPointerGreaterThan | Word32Equal | Uint64LessThan
    (* machine: memory *)
    | Store | Load
    (* machine: bitcast *)
    | BitcastTaggedToWord | BitcastWord32ToWord64 | BitcastWordToTagged
    | TruncateInt64ToInt32 ->
        failwith "Not implemented"
    | Empty -> (Value.empty, Bool.tr)
    | _ -> (Value.empty, Bool.tr)
  in
  let updated_rf = RegisterFile.add vid value rf in
  let updated_asrt = Bool.and_ (State.assertion state) assertion in
  let next_state = State.update next_pc updated_rf updated_asrt state in

  if State.is_final next_state then
    { next_state with retvar = Option.some (BitVec.init ~len:Value.len vid) }
  else next_state
