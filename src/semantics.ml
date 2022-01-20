module Value = struct
  type t = Int of int | Float of float | Address of int | Tagged of int

  let create_int i = Int i
  let create_addr addr = Address addr
  let create_tagged i = Tagged i

  let int32add t1 t2 =
    match (t1, t2) with
    | Int i1, Int i2 -> Int ((i1 + i2) mod Int.shift_left 1 32)
    | _, _ -> failwith "bad operand type"

  let type_of t =
    match t with
    | Int _ -> "Int"
    | Float _ -> "Float"
    | Address _ -> "Address"
    | Tagged _ -> "Tagged"

  let to_string t =
    match t with
    | Int i -> string_of_int i
    | Float f -> string_of_float f
    | Address addr -> Printf.sprintf "0x%x" addr
    | Tagged i -> string_of_int i
end

module RegisterFile = Map.Make (String)

let update_register_file id node params register_file =
  let instr = IR.Node.instr node in
  let opcode = Instr.opcode instr in
  let operands = Instr.operands instr in
  match opcode with
  | Int32Constant | Int64Constant ->
      assert (List.length operands = 1);
      let n = List.hd operands |> Operand.to_int in
      RegisterFile.add id (Value.create_int n) register_file
  | HeapConstant | ExternalConstant ->
      assert (List.length operands = 1);
      let re = Re.Pcre.regexp "(0x[0-9a-f]+)" in
      let addr =
        Re.Group.get (Re.exec re (List.hd operands |> Operand.to_str)) 1
        |> int_of_string
      in
      RegisterFile.add id (Value.create_addr addr) register_file
  | Return ->
      assert (List.length operands = 1);
      let input_id = Operand.get_nth_id operands 0 in
      let v = RegisterFile.find input_id register_file in
      RegisterFile.add id v register_file
  | CheckedTaggedSignedToInt32 ->
      assert (List.length operands = 1);
      let input_id = Operand.get_nth_id operands 0 in
      let v =
        match RegisterFile.find input_id register_file with
        | Tagged i -> Value.create_int i
        | _ -> failwith "bad operand type"
      in
      RegisterFile.add id v register_file
  | ChangeInt32ToTagged ->
      assert (List.length operands = 1);
      let input_id = Operand.get_nth_id operands 0 in
      let v =
        match RegisterFile.find input_id register_file with
        | Int i -> Value.create_tagged i
        | _ -> failwith "bad operand type"
      in
      RegisterFile.add id v register_file
  | Int32Add ->
      assert (List.length operands = 2);
      let left_id = Operand.get_nth_id operands 0 in
      let right_id = Operand.get_nth_id operands 1 in
      let left_v = RegisterFile.find left_id register_file in
      let right_v = RegisterFile.find right_id register_file in
      let v = Value.int32add left_v right_v in
      RegisterFile.add id v register_file
  | Parameter ->
      assert (List.length operands = 1);
      let param_idx = (List.hd operands |> Operand.to_int) - 1 in
      if 0 <= param_idx && param_idx < List.length params then
        let param = List.nth params param_idx |> int_of_string in
        RegisterFile.add id (Value.create_tagged param) register_file
      else register_file
  | Branch | StackPointerGreaterThan | Call | Checkpoint | EffectPhi | End
  | FrameState | IfFalse | IfTrue | LoadStackCheckOffset | Merge | Start
  | TypedStateValues | Load | Empty ->
      register_file
  | _ -> failwith "Unimplemented Opcode"

let get_return_value graph_lines graph params =
  let register_file = RegisterFile.empty in
  List.fold_left
    (fun rf line ->
      let id = IR.parse_id line in
      let node = IR.find_node id graph in
      update_register_file (string_of_int id) node params rf)
    register_file graph_lines

let print_return_value rv =
  RegisterFile.iter
    (fun key v ->
      print_endline
        ("#" ^ key ^ " (" ^ Value.type_of v ^ " : " ^ Value.to_string v ^ ")"))
    rv
