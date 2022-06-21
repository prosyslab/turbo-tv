open Z3utils

let value_to_string model mem value =
  let ty_str = value |> Value.ty_of |> Type.to_string model in
  match ty_str with
  | "bool" -> value |> Value.Bool.to_string model
  | "int32" -> value |> Value.Int32.to_string model
  (* | "uint32" -> value |> Uint32.to_string *)
  | "int64" -> value |> Value.Int64.to_string model
  (* | "uint64" -> value |> Uint64.to_string *)
  | "float64" -> value |> Value.Float64.to_string model
  | "pointer" ->
      Format.sprintf "Pointer(%s)" (value |> Value.Int64.to_string model)
  | "tagged_signed" -> value |> Value.TaggedSigned.to_string model
  | "tagged_pointer" ->
      Format.sprintf "%s => %s"
        (value |> Pointer.to_string model)
        (Objects.to_string model mem value)
  | "map_in_header" -> value |> Value.MapInHeader.to_string model
  | "empty" -> "empty"
  | _ -> failwith (Format.sprintf "print_value: not implemented for %s" ty_str)

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

    let prefix = if State.stage state = "before" then "b" else "a" in
    RegisterFile.prefix := prefix ^ "v";
    Control.ControlFile.prefix := prefix ^ "c";

    let value =
      RegisterFile.find (string_of_int pc) rf |> value_to_string model mem
    in
    let control =
      Control.ControlFile.find (string_of_int pc) cf |> Control.to_string model
    in

    match opcode with
    | Start | Branch | Merge | Return | IfFalse | IfTrue ->
        Format.printf "#%d:%s => \n  Control: %s\n" pc instr_s control;
        aux (pc + 1)
    | Phi ->
        Format.printf "#%d:%s => \n  Value: %s\n  Control: %s\n" pc instr_s
          value control;
        aux (pc + 1)
    | End -> Format.printf "\n"
    | _ ->
        Format.printf "#%d:%s => \n  Value: %s\n" pc instr_s value;
        aux (pc + 1)
  in

  aux 0