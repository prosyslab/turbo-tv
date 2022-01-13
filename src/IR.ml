module Node = struct
  type id = int
  type t = id * Instr.t

  let compare = compare
  let hash = Hashtbl.hash
  let equal = ( = )
  let create id instr = (id, instr)

  let label (id, instr) =
    let opcode, operands = instr in
    String.concat ":"
      [
        "#" ^ string_of_int id;
        Opcode.to_str opcode;
        Operand.str_of_operands operands;
      ]
end

module G = Graph.Persistent.Digraph.ConcreteBidirectional (Node)

let extract_edge_string line =
  let check_bracket_match left right =
    match (left, right) with
    | '(', ')' | '[', ']' | '<', '>' -> true
    | _ -> false
  in
  let s = Stack.create () in
  let result =
    String.fold_left
      (fun result ch ->
        if ch = '(' || ch = '[' || ch = '<' then Stack.push ch s
        else if ch = ')' || ch = ']' || ch = '>' then
          if check_bracket_match (Stack.top s) ch then Stack.pop s |> ignore
          else failwith "File has weird bracket";
        if Stack.length s = 1 && Stack.top s = '(' then
          String.cat result (String.make 1 ch)
        else result)
      "" line
  in
  let result_len = String.length result in
  String.sub result 1 (result_len - 1)

let add_edges node egde_string g =
  let from_nodes =
    StringLabels.split_on_char ~sep:' ' egde_string
    |> List.filter (fun s -> String.length s > 0)
  in
  List.fold_left
    (fun g from_node ->
      let id, instr = Instr.parse_instr from_node in
      G.add_edge g (Node.create id instr) node)
    g from_nodes

let lines_to_graph graph_lines =
  let g = G.empty in
  List.fold_left
    (fun g line ->
      let id, instr = Instr.parse_instr line in
      let node = Node.create id instr in
      let edge_string = extract_edge_string line in
      G.add_vertex g node |> add_edges node edge_string)
    g graph_lines

(** Graph Visualization *)
module Dot = Graph.Graphviz.Dot (struct
  include G

  let graph_attributes _ = []
  let default_vertex_attributes _ = []
  let vertex_name v = "\"" ^ String.escaped (Node.label v) ^ "\""
  let vertex_attributes _ = [ `Shape `Box ]
  let get_subgraph _ = None
  let default_edge_attributes _ = []
  let edge_attributes _ = []
end)

let generate_graph_output name g =
  let file = open_out_bin name in
  Dot.output_graph file g
