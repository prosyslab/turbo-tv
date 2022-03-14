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
  let len = 69
  let tylen = 5
  let smilen = 32
  let smimask = 0xffffffff

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
  let taggedpointer_ty = BitVecVal.of_int ~len:tylen 12
  let mapinheader_ty = BitVecVal.of_int ~len:tylen 13
  let taggedsigned_ty = BitVecVal.of_int ~len:tylen 14
  let anytagged_ty = BitVecVal.of_int ~len:tylen 15
  let compressedpointer_ty = BitVecVal.of_int ~len:tylen 16
  let anycompressed_ty = BitVecVal.of_int ~len:tylen 17
  let sandboxedpointer_ty = BitVecVal.of_int ~len:tylen 18
  let bool_ty = BitVecVal.of_int ~len:tylen 19
  let none_ty = BitVecVal.of_int ~len:tylen 20
  let ty_of t = BitVec.extract 0 tylen t
  let data_of t = BitVec.extract tylen len t

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

  let is_taggedsigned value =
    let value_ty = ty_of value in
    BitVec.eqb value_ty taggedsigned_ty

  (* comparison *)
  let is_equal lval rval = Bool.ands [ BitVec.eqb lval rval ]

  (* typing *)
  let data_to_int32 data = BitVec.concat int32_ty data
  let data_to_int64 data = BitVec.concat int64_ty data
  let data_to_pointer data = BitVec.concat pointer_ty data
  let data_to_taggedsigned data = BitVec.concat taggedsigned_ty data

  (* constant assignment *)
  let of_int32 vid c =
    let value = BitVec.init vid in
    let cval = BitVec.concat int32_ty (BitVecVal.of_str c) in
    let assertion = Bool.ands [ is_equal value cval ] in
    (value, assertion)

  let of_int64 vid c =
    let value = BitVec.init vid in
    let cval = BitVec.concat int64_ty (BitVecVal.of_str c) in
    let assertion = Bool.ands [ is_equal value cval ] in
    (value, assertion)

  let of_pointer vid c =
    let value = BitVec.init vid in
    let cval = BitVec.concat pointer_ty (BitVecVal.of_str c) in
    let assertion = Bool.ands [ is_equal value cval ] in
    (value, assertion)

  let of_taggedsigned vid c =
    let value = BitVec.init vid in
    let cval = BitVec.concat taggedsigned_ty (BitVecVal.of_str c) in
    let assertion = Bool.ands [ is_equal value cval ] in
    (value, assertion)

  (* var = (lval + rval) mod 2^32 *)
  let int32add vid lval rval =
    let value = BitVec.init vid in

    let ldata = data_of lval in
    let rdata = data_of rval in
    let res = BitVec.andi (BitVec.addb ldata rdata) smimask |> data_to_int32 in

    let assertion =
      Bool.ands [ is_int32 lval; is_int32 rval; is_equal value res ]
    in

    (value, assertion)

  (* var = pval >> 32 *)
  let checked_tagged_signed_to_i32 vid pval = failwith "Not implemented"

  (* var = pvar << 32 *)
  let i32_to_tagged vid pval = failwith "Not implemented"
  let parameter vid param = failwith "Not implemented"
  let return vid pval = failwith "Not implemented"
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
  let print t = failwith "Not implemented"
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
  set_bvlen Value.len;

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
        let addr_re = Re.Pcre.regexp "(0x[0-9a-f]*)" in
        let operand = Operands.const_of_nth operands 0 in
        Re.Group.get (Re.exec addr_re operand) 1 |> Value.of_pointer vid
    | Int32Constant -> Operands.const_of_nth operands 0 |> Value.of_int32 vid
    | Int64Constant -> Operands.const_of_nth operands 0 |> Value.of_int64 vid
    | NumberConstant
    (* common: control *)
    | Branch | Projection ->
        failwith "Not implemented"
    (* common: procedure *)
    | Parameter ->
        let pidx = Operands.const_of_nth operands 0 |> int_of_string in
        if 0 < pidx && pidx <= List.length params then
          let param = List.nth params (pidx - 1) in
          Value.parameter vid param
        else (Value.empty, Bool.tr)
    | Return | Call | End
    (* simplified: arithmetic *)
    | SpeculativeSafeIntegerAdd
    (* simplified: memory *)
    | AllocateRaw | StoreField
    (* simplified: type-conversion *)
    | ChangeInt32ToTagged | ChangeInt32ToFloat64 | CheckedTaggedSignedToInt32 ->
        failwith "Not implemented"
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
    { next_state with retvar = Option.some (BitVec.init vid) }
  else next_state
