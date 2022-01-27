open Err

module Value = struct
  type t =
    | Bit of int
    | Float64 of float
    | Int31 of int
    | Int32 of int
    | BigInt of int
    | UInt32 of int
    | Int64 of int
    | Tagged of int
    | TaggedSigned of int
    | TaggedPointer of int
    | Addr of int
    | Empty

  let of_int32 i = Int32 i
  let of_int64 i = Int64 i
  let of_addr p = Addr p
  let of_tagged i = Tagged i
  let of_tagged_signed i = TaggedSigned i

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

  let is_type_of v t = v |> type_of = t

  let to_str v =
    match v with
    | Bit b -> string_of_int b
    | Float64 f -> string_of_float f
    | Int31 i | Int32 i | Int64 i | BigInt i | UInt32 i -> string_of_int i
    | Tagged i | TaggedSigned i | TaggedPointer i -> string_of_int i
    | Addr p -> Printf.sprintf "0x%x" p
    | Empty -> ""

  let is_true v =
    match v with
    | Int31 i | Int32 i | UInt32 i | Int64 i -> if i = 0 then false else true
    | _ ->
        let cause = v |> to_str in
        let reason =
          Format.sprintf "Value `%s` cannot be evaluated as boolean" cause
        in
        err (TypeMismatch (cause, reason))

  let tagged_to_i32 v =
    match v with
    | Tagged t -> of_int32 t
    | _ ->
        let cause = v |> to_str in
        let reason =
          Format.sprintf "Value `%s` is not type of `%s`" cause "Tagged"
        in
        err (TypeMismatch (cause, reason))
    
  let tagged_signed_to_i32 v =
    match v with
    | TaggedSigned t -> of_int32 t
    | _ ->
        let cause = v |> to_str in
        let reason =
          Format.sprintf "Value `%s` is not type of `%s`" cause "TaggedSigned"
        in
        err (TypeMismatch (cause, reason))

  let i32_to_tagged v =
    match v with
    | Int32 t -> of_tagged t
    | _ ->
        let cause = v |> to_str in
        let reason =
          Format.sprintf "Value `%s` is not type of `%s`" cause "Int32"
        in
        err (TypeMismatch (cause, reason))

  let int32add v1 v2 =
    match (v1, v2) with
    | Int32 i1, Int32 i2 -> Int32 ((i1 + i2) mod Int.shift_left 1 32)
    | _, _ -> failwith "bad operand type"
end

module RegisterFile = struct
  module R = Map.Make (String)

  let add = R.add

  let find id rf =
    try R.find id rf
    with Not_found ->
      let cause = id in
      let reason = Format.sprintf "Cannot find #%s from RegisterFile" cause in
      err (IdNotFound (cause, reason))

  let find_type_of id ty register_type =
    let v = find id register_type in
    if Value.is_type_of v ty then v
    else
      let cause = v |> Value.to_str in
      let reason = Format.sprintf "Value `%s` is not type of `%s`" cause ty in
      err (TypeMismatch (cause, reason))

  let empty = R.empty
  let iter = R.iter
end

module State = struct
  type t = {
    pc : IR.Node.id;
    rf : Value.t RegisterFile.R.t;
    params : string list;
    return_value : Value.t;
  }

  let init params =
    { pc = 0; rf = RegisterFile.empty; params; return_value = Value.Empty }

  (* getter *)
  let pc t = t.pc
  let rf t = t.rf
  let params t = t.params
  let return_value t = t.return_value
  let update rf pc t = { t with rf; pc }
  let is_final t = t.pc = -1

  let print_register_file t =
    RegisterFile.iter
      (fun key v ->
        print_endline
          ("#" ^ key ^ " (" ^ Value.type_of v ^ " : " ^ Value.to_str v ^ ")"))
      t.rf
end

let apply program state =
  let pc = State.pc state in
  let rf = State.rf state in
  print_endline (string_of_int pc);

  let opcode, operands = IR.instr_of pc program in
  let next_pc =
    match opcode with
    | Branch ->
        let b_id = Operands.id_of_nth operands 0 in
        let b = RegisterFile.find b_id rf in

        if b |> Value.is_true then IR.true_br_of pc program
        else IR.false_br_of pc program
    | Return -> -1
    | _ -> pc + 1
  in

  let value =
    match opcode with
    | Int32Constant -> Operands.int_of_nth operands 0 |> Value.of_int32
    | Int64Constant -> Operands.int_of_nth operands 0 |> Value.of_int64
    | HeapConstant | ExternalConstant ->
        Operands.addr_of_nth operands 0 |> Value.of_addr
    | Return ->
        let k = Operands.id_of_nth operands 0 in
        RegisterFile.find k rf
    | CheckedTaggedSignedToInt32 ->
        let k = Operands.id_of_nth operands 0 in
        let v = RegisterFile.find_type_of k "TaggedSigned" rf in
        Value.tagged_signed_to_i32 v
    | ChangeInt32ToTagged ->
        let k = Operands.id_of_nth operands 0 in
        let v = RegisterFile.find_type_of k "Int32" rf in
        Value.i32_to_tagged v
    | Int32Add ->
        let lid = Operands.id_of_nth operands 0 in
        let rid = Operands.id_of_nth operands 1 in
        let lv = RegisterFile.find_type_of lid "Int32" rf in
        let rv = RegisterFile.find_type_of rid "Int32" rf in
        Value.int32add lv rv
    | Parameter ->
        let params = State.params state in
        let param_idx = Operands.int_of_nth operands 0 - 1 in

        if 0 <= param_idx && param_idx < List.length params then
          let param = List.nth params param_idx |> int_of_string in
          Value.of_tagged_signed param
        else Value.Empty
    | StackPointerGreaterThan ->
        (* TODO: implement StackPointerGreaterThan *)
        Value.of_int32 1
    | Branch -> Value.Empty
    (* Unimplemented *)
    | Call | Checkpoint | EffectPhi | End | FrameState | IfFalse | IfTrue
    | LoadStackCheckOffset | Merge | Start | TypedStateValues | Load | Empty ->
        Value.Empty
    | _ -> Value.Empty
  in
  let updated_rf = RegisterFile.add (pc |> string_of_int) value rf in
  let next_state = State.update updated_rf next_pc state in

  if opcode = Return then {next_state with return_value=value}
  else next_state