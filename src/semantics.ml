module Value = struct
  type t = Int of int | Float of float | Address of int | Tagged of int
  [@@deriving equal]

  let create_int i = Int i
  let create_addr addr = Address addr
  let create_tagged i = Tagged i

  let int32add t1 t2 =
    match (t1, t2) with
    | Int i1, Int i2 -> Int ((i1 + i2) mod Int.shift_left 1 32)
    | _, _ -> failwith "bad operand type"

  let eval_bool t =
    match t with
    | Int i -> if i = 0 then false else true
    | _ -> failwith "bad operand type"

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

module State = struct
  type t = {
    pc : int;
    rf : Value.t RegisterFile.t;
    graph_lines : string list;
    graph : IR.G.t;
    params : string list;
    return_value : Value.t Option.t;
  }

  let pc t = t.pc
  let params t = t.params
  let return_value t = t.return_value

  let init graph_lines graph params =
    {
      pc = 0;
      rf = RegisterFile.empty;
      graph_lines;
      graph;
      params;
      return_value = None;
    }

  let get_id t =
    let line = List.nth t.graph_lines t.pc in
    IR.parse_id line |> string_of_int

  let get_node t =
    let id = get_id t |> int_of_string in
    IR.find_node id t.graph

  let get_instr t =
    let node = get_node t in
    IR.Node.instr node

  let get_tf_addr t =
    let find_node opcode nodes =
      List.find
        (fun node ->
          let node_opcode = IR.Node.instr node |> Instr.opcode in
          opcode = node_opcode)
        nodes
    in
    let node = get_node t in
    let next_nodes = IR.G.succ t.graph node in
    let true_node = find_node Opcode.IfTrue next_nodes in
    let false_node = find_node Opcode.IfFalse next_nodes in
    (IR.Node.address true_node, IR.Node.address false_node)

  let update_rf id value t =
    let rf = t.rf in
    { t with rf = RegisterFile.add id value rf }

  let find_rf id t = RegisterFile.find id t.rf

  let update_pc ?pc t =
    match pc with Some pc -> { t with pc } | None -> { t with pc = t.pc + 1 }

  let program_ends t =
    if 0 <= t.pc && t.pc < List.length t.graph_lines then false else true

  let print_register_file t =
    RegisterFile.iter
      (fun key v ->
        print_endline
          ("#" ^ key ^ " (" ^ Value.type_of v ^ " : " ^ Value.to_string v ^ ")"))
      t.rf
end

let next_state state =
  let pc = State.pc state in
  print_endline (string_of_int pc);
  let id = State.get_id state in
  let instr = State.get_instr state in
  let opcode = Instr.opcode instr in
  let operands = Instr.operands instr in
  match opcode with
  | Int32Constant | Int64Constant ->
      assert (List.length operands = 1);
      let n = List.hd operands |> Operand.to_int in
      state |> State.update_rf id (Value.create_int n) |> State.update_pc
  | HeapConstant | ExternalConstant ->
      assert (List.length operands = 1);
      let re = Re.Pcre.regexp "(0x[0-9a-f]+)" in
      let addr =
        Re.Group.get (Re.exec re (List.hd operands |> Operand.to_str)) 1
        |> int_of_string
      in
      state |> State.update_rf id (Value.create_addr addr) |> State.update_pc
  | Return ->
      assert (List.length operands = 1);
      let input_id = Operand.get_nth_id operands 0 in
      let v = State.find_rf input_id state in
      state |> State.update_rf id v |> State.update_pc ~pc:(-1)
  | CheckedTaggedSignedToInt32 ->
      assert (List.length operands = 1);
      let input_id = Operand.get_nth_id operands 0 in
      let v =
        match State.find_rf input_id state with
        | Tagged i -> Value.create_int i
        | _ -> failwith "bad operand type"
      in
      state |> State.update_rf id v |> State.update_pc
  | ChangeInt32ToTagged ->
      assert (List.length operands = 1);
      let input_id = Operand.get_nth_id operands 0 in
      let v =
        match State.find_rf input_id state with
        | Int i -> Value.create_tagged i
        | _ -> failwith "bad operand type"
      in
      state |> State.update_rf id v |> State.update_pc
  | Int32Add ->
      assert (List.length operands = 2);
      let left_id = Operand.get_nth_id operands 0 in
      let right_id = Operand.get_nth_id operands 1 in
      let left_v = State.find_rf left_id state in
      let right_v = State.find_rf right_id state in
      let v = Value.int32add left_v right_v in
      state |> State.update_rf id v |> State.update_pc
  | Parameter ->
      assert (List.length operands = 1);
      let params = State.params state in
      let param_idx = (List.hd operands |> Operand.to_int) - 1 in
      (if 0 <= param_idx && param_idx < List.length params then
       let param = List.nth params param_idx |> int_of_string in
       state |> State.update_rf id (Value.create_tagged param)
      else state)
      |> State.update_pc
  | StackPointerGreaterThan ->
      (* TODO: implement StackPointerGreaterThan *)
      state |> State.update_rf id (Value.create_int 1) |> State.update_pc
  | Branch ->
      assert (List.length operands = 1);
      let input_id = Operand.get_nth_id operands 0 in
      let b = State.find_rf input_id state |> Value.eval_bool in
      let true_addr, false_addr = State.get_tf_addr state in
      if b then state |> State.update_pc ~pc:true_addr
      else state |> State.update_pc ~pc:false_addr
  (* Unimplemented *)
  | Call | Checkpoint | EffectPhi | End | FrameState | IfFalse | IfTrue
  | LoadStackCheckOffset | Merge | Start | TypedStateValues | Load | Empty ->
      state |> State.update_pc
  | _ -> state |> State.update_pc

let rec execute state =
  if State.program_ends state then state else execute (next_state state)

let get_return_value graph_lines graph params =
  let init_state = State.init graph_lines graph params in
  let final_state = execute init_state in
  State.return_value final_state
