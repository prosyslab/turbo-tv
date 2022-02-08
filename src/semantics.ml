open Err
open Z3utils

module Params = struct
  module Param = struct
    type t = BitVec.t

    let init pid = BitVec.init pid
  end

  type t = Param.t list

  let init nparams =
    let rec mk_param cnt res =
      if cnt == nparams then res
      else mk_param (cnt + 1) (Param.init ("p" ^ (cnt |> string_of_int)) :: res)
    in
    mk_param 0 []
end

module Value = struct
  type id = string

  type t =
    | Bit of BitVec.t
    | Float64 of BitVec.t
    | Int31 of BitVec.t
    | Int32 of BitVec.t
    | BigInt of BitVec.t
    | UInt32 of BitVec.t
    | Int64 of BitVec.t
    | Tagged of BitVec.t
    | TaggedSigned of BitVec.t
    | TaggedPointer of BitVec.t
    | Addr of BitVec.t
    | Empty

  let type_of t =
    match t with
    | Bit _ -> "Bit"
    | Float64 _ -> "Float64"
    | Int31 _ -> "Int31"
    | Int32 _ -> "Int32"
    | BigInt _ -> "BigInt"
    | UInt32 _ -> "UInt32"
    | Int64 _ -> "Int64"
    | Tagged _ -> "Tagged"
    | TaggedSigned _ -> "TaggedSigned"
    | TaggedPointer _ -> "TaggedPointer"
    | Addr _ -> "Addr"
    | Empty -> "Empty"

  let to_str t =
    match t with
    | Empty -> ""
    | Bit exp
    | Float64 exp
    | Int31 exp
    | Int32 exp
    | BigInt exp
    | UInt32 exp
    | Int64 exp
    | Tagged exp
    | TaggedSigned exp
    | TaggedPointer exp
    | Addr exp ->
        str_of_exp exp

  let bv t =
    match t with
    | Bit bv
    | Float64 bv
    | Int31 bv
    | Int32 bv
    | BigInt bv
    | UInt32 bv
    | Int64 bv
    | Tagged bv
    | TaggedSigned bv
    | TaggedPointer bv
    | Addr bv ->
        bv
    | Empty -> Bool.tr

  (* constants *)
  let len = 64
  let smilen = 32
  let smimask = 0xffffffff

  (* assignment *)
  let of_int32 vid c =
    let var = BitVec.init vid in
    let value = Int32 var in
    let assertion = BitVec.eqb var (BitVecVal.of_str c) in
    (value, assertion)

  let of_int64 vid c =
    let var = BitVec.init vid in
    let value = Int64 var in
    let assertion = BitVec.eqb var (BitVecVal.of_str c) in
    (value, assertion)

  let of_addr vid c =
    let var = BitVec.init vid in
    let value = Addr var in
    let assertion = BitVec.eqb var (BitVecVal.of_str c) in
    (value, assertion)

  let of_tagged vid c =
    let var = BitVec.init vid in
    let value = Tagged var in
    let assertion = BitVec.eqb var (BitVecVal.of_str c) in
    (value, assertion)

  let of_tagged_signed vid c =
    let var = BitVec.init vid in
    let value = TaggedSigned var in
    let assertion = BitVec.eqb var (BitVecVal.of_str c) in
    (value, assertion)

  (* var = (lpvar + rpvar) mod 2^32 *)
  let int32add vid lval rval =
    let var = BitVec.init vid in
    let value = Int32 var in
    match (lval, rval) with
    | Int32 lbv, Int32 rbv ->
        let assertion =
          BitVec.eqb var (BitVec.andi (BitVec.addb lbv rbv) smimask)
        in
        (value, assertion)
    | _ ->
        let cause = (lval |> to_str) ^ " or " ^ (rval |> to_str) in
        let reason = Format.sprintf "%s is not type of 'Int32'" cause in
        err (TypeMismatch (cause, reason))

  (* var = pvar >> 32 *)
  let tagged_signed_to_i32 vid pval =
    let var = BitVec.init vid in
    let value = Int32 var in
    match pval with
    | TaggedSigned bv ->
        let assertion = BitVec.eqb var (BitVec.ashri bv smilen) in
        (value, assertion)
    | _ ->
        let cause = pval |> to_str in
        let reason = Format.sprintf "%s is not type of 'TaggedSigned'" cause in
        err (TypeMismatch (cause, reason))

  (* var = pvar << 32 *)
  let i32_to_tagged vid pval =
    let var = BitVec.init vid in
    let value = Tagged var in
    match pval with
    | Int32 bv ->
        let assertion = BitVec.eqb var (BitVec.shli bv smilen) in
        (value, assertion)
    | _ ->
        let cause = pval |> to_str in
        let reason = Format.sprintf "%s is not type of 'Int32'" cause in
        err (TypeMismatch (cause, reason))

  let parameter vid param =
    let var = BitVec.init vid in
    let value = TaggedSigned var in
    let assertion = BitVec.eqb var param in
    (value, assertion)

  let return vid pval =
    let var = BitVec.init vid in
    let assertion = BitVec.eqb var (pval |> bv) in
    (Empty, assertion)
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

  let print t =
    iter
      (fun key v ->
        print_endline
          ("#" ^ key ^ " (" ^ Value.type_of v ^ " : " ^ Value.to_str v ^ ")"))
      t
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
    | Int32Constant -> Operands.const_of_nth operands 0 |> Value.of_int32 vid
    | Int64Constant -> Operands.const_of_nth operands 0 |> Value.of_int64 vid
    | HeapConstant | ExternalConstant ->
        let addr_re = Re.Pcre.regexp "(0x[0-9a-f]*)" in
        let operand = Operands.const_of_nth operands 0 in
        Re.Group.get (Re.exec addr_re operand) 1 |> Value.of_addr vid
    | CheckedTaggedSignedToInt32 ->
        let pid = prefix ^ Operands.id_of_nth operands 0 in
        let pval = RegisterFile.find pid rf in
        Value.tagged_signed_to_i32 vid pval
    | ChangeInt32ToTagged ->
        let pid = prefix ^ Operands.id_of_nth operands 0 in
        let pval = RegisterFile.find pid rf in
        Value.i32_to_tagged vid pval
    | Int32Add ->
        let lpid = prefix ^ Operands.id_of_nth operands 0 in
        let rpid = prefix ^ Operands.id_of_nth operands 1 in
        let lval = RegisterFile.find lpid rf in
        let rval = RegisterFile.find rpid rf in
        Value.int32add vid lval rval
    | StackPointerGreaterThan ->
        (* TODO: implement StackPointerGreaterThan *)
        Value.of_int32 vid "1"
    | Parameter ->
        let pidx = Operands.const_of_nth operands 0 |> int_of_string in
        if 0 < pidx && pidx <= List.length params then
          let param = List.nth params (pidx - 1) in
          Value.parameter vid param
        else (Value.Empty, Bool.tr)
    | Return ->
        let pid = prefix ^ Operands.id_of_nth operands 0 in
        let pval = RegisterFile.find pid rf in
        Value.return vid pval
    | Branch -> (Value.Empty, Bool.tr)
    (* Unimplemented *)
    | Call | Checkpoint | EffectPhi | End | FrameState | IfFalse | IfTrue
    | Empty ->
        (Value.Empty, Bool.tr)
    | _ -> (Value.Empty, Bool.tr)
  in
  let updated_rf = RegisterFile.add vid value rf in
  let updated_asrt = Bool.and_ (State.assertion state) assertion in
  let next_state = State.update next_pc updated_rf updated_asrt state in

  if State.is_final next_state then
    { next_state with retvar = Option.some (BitVec.init vid) }
  else next_state
