open Err
open Z3utils

module Value = struct
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

  let vlen = 64
  let smilen = 32

  let of_int32 pc v =
    let var = BitVec.init pc in
    let value = BitVecVal.of_str v in
    Int32 (BitVec.eqb var value)

  let of_int64 pc v =
    let var = BitVec.init pc in
    let value = BitVecVal.of_str v in
    Int64 (BitVec.eqb var value)

  let of_addr pc v =
    let var = BitVec.init pc in
    let addr = BitVecVal.of_str v in
    Addr (BitVec.eqb var addr)

  let of_tagged pc v =
    let var = BitVec.init pc in
    let value = BitVecVal.of_str v in
    Tagged (BitVec.eqb var value)

  let of_tagged_signed pc v =
    let var = BitVec.init pc in
    let value = BitVecVal.of_str v in
    TaggedSigned (BitVec.eqb var value)

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

  let is_type_of t ty = t |> type_of = ty

  let to_str t =
    match t with
    | Bit e
    | Float64 e
    | Int31 e
    | Int32 e
    | BigInt e
    | UInt32 e
    | Int64 e
    | Tagged e
    | TaggedSigned e
    | TaggedPointer e
    | Addr e ->
        Z3.Expr.to_string e
    | Empty -> ""

  let expr t =
    match t with
    | Bit e
    | Float64 e
    | Int31 e
    | Int32 e
    | BigInt e
    | UInt32 e
    | Int64 e
    | Tagged e
    | TaggedSigned e
    | TaggedPointer e
    | Addr e ->
        e
    | Empty -> Z3.Boolean.mk_or ctx [ Z3.Boolean.mk_true ctx ]

  let is_true t =
    match t with
    | Int31 e | Int32 e | UInt32 e | Int64 e -> BitVec.is_true e
    | _ ->
        let cause = t |> to_str in
        let reason =
          Format.sprintf "Value `%s` cannot be evaluated as boolean" cause
        in
        err (TypeMismatch (cause, reason))

  let eq lval rval = Int64 (BitVec.eqb (BitVec.init lval) (BitVec.init rval))

  let int32add pc lid rid =
    let var = BitVec.init pc in
    let lvar = BitVec.init lid in
    let rvar = BitVec.init rid in
    let value = Z3.BitVector.mk_add ctx lvar rvar in
    Int32 (BitVec.eqb var value)

  let tagged_signed_to_i32 pc operand =
    let var = BitVec.init pc in
    let value = BitVec.ashri (BitVec.init operand) smilen in
    Int32 (BitVec.eqb var value)

  let i32_to_tagged pc operand =
    let var = BitVec.init pc in
    let value = BitVec.shli (BitVec.init operand) smilen in
    Tagged (BitVec.eqb var value)
end

module State = struct
  type t = {
    pc : IR.Node.id;
    params : string list;
    retexp : BitVec.t;
    retvar : BitVec.t Option.t;
  }

  let init params =
    {
      pc = 0;
      params;
      retexp = Z3.Boolean.mk_or ctx [ Z3.Boolean.mk_true ctx ];
      retvar = None;
    }

  (* getter *)
  let pc t = t.pc
  let params t = t.params
  let return_expr t = t.retexp
  let update pc rv t = { t with pc; retexp = rv }
  let is_final t = t.pc = -1
end

let apply program state prefix =
  let pc = State.pc state in
  let pc_str = prefix ^ string_of_int pc in

  let opcode, operands = IR.instr_of pc program in
  let next_pc =
    match opcode with
    (* ignore branch for now *)
    (* | Branch ->
           let b_id = Operands.id_of_nth operands 0 in
           let b = RegisterFile.find b_id rf in

           if b |> Value.is_true then IR.true_br_of pc program
           else IR.false_br_of pc program *)
    | Return -> -1
    | _ -> pc + 1
  in

  let value =
    match opcode with
    | Int32Constant -> Operands.const_of_nth operands 0 |> Value.of_int32 pc_str
    | Int64Constant -> Operands.const_of_nth operands 0 |> Value.of_int64 pc_str
    | HeapConstant | ExternalConstant ->
        let addr_re = Re.Pcre.regexp "(0x[0-9a-f]*)" in
        let operand = Operands.const_of_nth operands 0 in
        Re.Group.get (Re.exec addr_re operand) 1 |> Value.of_addr pc_str
    | CheckedTaggedSignedToInt32 ->
        let k = Operands.id_of_nth operands 0 in
        Value.tagged_signed_to_i32 pc_str (prefix ^ k)
    | ChangeInt32ToTagged ->
        let k = Operands.id_of_nth operands 0 in
        Value.i32_to_tagged pc_str (prefix ^ k)
    | Int32Add ->
        let lid = Operands.id_of_nth operands 0 in
        let rid = Operands.id_of_nth operands 1 in
        Value.int32add pc_str (prefix ^ lid) (prefix ^ rid)
    | Parameter ->
        let params = State.params state in
        let param_idx = Operands.int_of_nth operands 0 - 1 in

        if 0 <= param_idx && param_idx < List.length params then
          let param = List.nth params param_idx in
          Value.of_tagged_signed pc_str param
        else Value.Empty
    | StackPointerGreaterThan ->
        (* TODO: implement StackPointerGreaterThan *)
        Value.of_int32 pc_str "1"
    | Return ->
        let k = Operands.id_of_nth operands 0 in
        Value.eq pc_str (prefix ^ k)
    | Branch -> Value.Empty
    (* Unimplemented *)
    | Call | Checkpoint | EffectPhi | End | FrameState | IfFalse | IfTrue
    | Empty ->
        Value.Empty
    | _ -> Value.Empty
  in

  let rv = Z3.Boolean.mk_and ctx [ state.retexp; value |> Value.expr ] in

  let next_state = State.update next_pc rv state in

  if State.is_final next_state then
    { next_state with retvar = Option.some (BitVec.init pc_str) }
  else next_state
