open Z3utils
open ValueOperator
module Objects = Memory.Objects 
let to_string model mem ptr =
  let map = Objects.map_of ptr mem in
  let map_str = map |> Objmap.to_string model in
  match map_str with
  | "heap_number" ->
      let obj = Heapnumber.load ptr mem in
      Heapnumber.to_string model obj
  | "big_int" ->
      let obj = Bigint.load ptr mem in
      Bigint.to_string model obj
  | "string" ->
      let obj = Strings.load ptr mem in
      Strings.to_string model obj
  | s -> s ^ " object: not implemented yet"


let value_to_string model rf mem value =
  let ty_str = value |> Value.ty_of |> Type.to_string model in
  match ty_str with
  | "bool" -> value |> Boolean.to_string model
  | "int8" -> value |> Int8.to_string model
  | "int32" -> value |> Int32.to_string model
  | "int64" -> value |> Int64.to_string model
  | "uint32" -> value |> Uint32.to_string model
  | "uint64" -> value |> Uint64.to_string model
  | "float64" -> value |> Float64.to_string model
  | "pointer" -> Format.sprintf "Pointer(%s)" (value |> Int64.to_string model)
  | "tagged_signed" -> value |> TaggedSigned.to_string model
  | "tagged_pointer" ->
      Format.sprintf "%s => %s"
        (value |> TaggedPointer.to_string model)
        (if value |> Constant.is_constant_ptr model rf then
         value |> Constant.to_string model rf
        else to_string model mem value)
  | "any_tagged" -> (
      try
        let is_tagged_signed =
          Bool.eq (BitVec.extract 0 0 value) (BitVecVal.from_int ~len:1 0)
          |> Model.eval model |> Expr.to_simplified_string |> bool_of_string
        in
        if is_tagged_signed then value |> TaggedSigned.to_string model
        else
          Format.sprintf "%s => %s"
            (value |> TaggedPointer.to_string model)
            (to_string model mem value)
      with _ -> value |> Model.eval model |> Expr.to_simplified_string)
  | "map_in_header" -> value |> MapInHeader.to_string model
  | "undefined" -> "undefined"
  | "empty" -> "empty"
  | _ -> ty_str ^ (value |> Model.eval model |> Expr.to_simplified_string)

let print_params model rf mem params =
  Format.printf "Parameters: \n";
  List.iteri
    (fun idx param ->
      let param_str =
        try param |> value_to_string model rf mem
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
      RegisterFile.find (string_of_int pc) rf |> value_to_string model rf mem
    in
    let control =
      ControlFile.find (string_of_int pc) cf |> Control.to_string model
    in
    let ub = State.UBFile.find (string_of_int pc) uf |> Ub.to_string model in
    let deopt =
      State.DeoptFile.find (string_of_int pc) df |> Deopt.to_string model
    in

    match opcode with
    | End ->
        Format.printf
          "#%d:%s => \n\
          \  Value: %s\n\
          \  ControlToken: %s\n\
          \  UB: %s\n\
          \  Deopt: %s\n\n"
          pc instr_s value control ub deopt
    | _ ->
        Format.printf
          "#%d:%s => \n  Value: %s\n  ControlToken: %s\n  UB: %s\n  Deopt: %s\n"
          pc instr_s value control ub deopt;
        aux (pc + 1)
  in

  aux 0