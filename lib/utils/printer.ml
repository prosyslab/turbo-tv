open Z3utils

let value_to_string model mem value =
  let ty_str = value |> Value.ty_of |> Type.to_string model in
  match ty_str with
  | "bool" -> value |> Value.Bool.to_string model
  | "int8" -> value |> Value.Int8.to_string model
  | "int32" -> value |> Value.Int32.to_string model
  (* | "uint32" -> value |> Uint32.to_string *)
  | "int64" -> value |> Value.Int64.to_string model
  | "uint32" -> value |> Value.Uint32.to_string model
  | "uint64" -> value |> Value.Uint64.to_string model
  (* | "uint64" -> value |> Uint64.to_string *)
  | "float64" -> value |> Float64.to_string model
  | "pointer" ->
      Format.sprintf "Pointer(%s)" (value |> Value.Int64.to_string model)
  | "tagged_signed" -> value |> Value.TaggedSigned.to_string model
  | "tagged_pointer" ->
      Format.sprintf "%s => %s"
        (value |> TaggedPointer.to_string model)
        (Objects.to_string model mem value)
  | "any_tagged" -> (
      try
        let is_tagged_signed =
          Bool.eq (BitVec.extract 0 0 value) (BitVecVal.from_int ~len:1 0)
          |> Model.eval model |> Expr.to_simplified_string |> bool_of_string
        in
        if is_tagged_signed then value |> Value.TaggedSigned.to_string model
        else
          Format.sprintf "%s => %s"
            (value |> TaggedPointer.to_string model)
            (Objects.to_string model mem value)
      with _ -> value |> Model.eval model |> Expr.to_simplified_string)
  | "map_in_header" -> value |> Value.MapInHeader.to_string model
  | "empty" -> "empty"
  | _ -> ty_str ^ (value |> Model.eval model |> Expr.to_simplified_string)

let print_params model mem params =
  Format.printf "Parameters: \n";
  List.iteri
    (fun idx param ->
      let param_str =
        try param |> value_to_string model mem
        with _ -> param |> Model.eval model |> Expr.to_string
      in
      Format.printf "Parameter[%d]: %s\n" idx param_str)
    params;
  Format.printf "\n"

let print_counter_example program state model =
  Format.printf "State of %s\n" (State.stage state);
  let rf = State.register_file state in
  let cf = State.control_file state in
  let uf = State.ub_file state in
  let df = State.deopt_file state in
  let mem = State.memory state in
  let rec aux pc =
    let ty, opcode, operands = IR.instr_of pc program in
    let instr_s =
      match ty with
      | Some ty ->
          Format.sprintf "%s(%s) [%s]" (opcode |> Opcode.to_str)
            (operands |> Operands.to_str)
            (ty |> Types.to_string)
      | None ->
          Format.sprintf "%s(%s)" (opcode |> Opcode.to_str)
            (operands |> Operands.to_str)
    in

    let value =
      RegisterFile.find (string_of_int pc) rf |> value_to_string model mem
    in
    let control =
      ControlFile.find (string_of_int pc) cf |> Control.to_string model
    in
    let ub = State.UBFile.find (string_of_int pc) uf |> Ub.to_string model in
    let deopt =
      State.DeoptFile.find (string_of_int pc) df |> Deopt.to_string model
    in

    match opcode with
    | Start | Branch | Merge | IfFalse | IfTrue | JSStackCheck | DeoptimizeIf
    | DeoptimizeUnless ->
        Format.printf "#%d:%s => \n  Control: %s\n  UB: %s\n  Deopt: %s\n" pc
          instr_s control ub deopt;
        aux (pc + 1)
    | Return ->
        Format.printf
          "#%d:%s => \n  Value: %s\n  Control: %s\n  UB: %s\n  Deopt: %s\n" pc
          instr_s value control ub deopt;
        aux (pc + 1)
    | End ->
        Format.printf "#%d:%s => \n  Value: %s\n  UB: %s\n  Deopt: %s\n\n" pc
          instr_s value ub deopt
    | _ ->
        Format.printf "#%d:%s => \n  Value: %s\n  UB: %s\n  Deopt: %s\n" pc
          instr_s value ub deopt;
        aux (pc + 1)
  in

  aux 0