open Err

module Node = struct
  type id = int

  type t = id * Instr.t

  let compare = compare

  let hash = Hashtbl.hash

  let equal = ( = )

  let create id instr : t = (id, instr)

  let empty = (-1, Instr.empty)

  let id (id, _) : id = id

  let instr (_, instr) : Instr.t = instr

  let label node =
    let id, instr = node in
    let opcode = instr |> Instr.opcode in
    let operands = instr |> Instr.operands in
    Printf.sprintf "#%d:%s(%s)" id (Opcode.to_str opcode)
      (Operands.to_str operands)
end

module Edge = struct
  type t = Value | Effect | Control

  let default = Value

  let to_int t = match t with Value -> 0 | Effect -> 1 | Control -> 2

  let compare t1 t2 = compare (to_int t1) (to_int t2)

  let value = Value

  let effect = Effect

  let control = Control

  let to_str t =
    match t with Value -> "Value" | Effect -> "Effect" | Control -> "Control"

  let is_control t = match t with Control -> true | _ -> false
end

module G = Graph.Persistent.Digraph.ConcreteBidirectionalLabeled (Node) (Edge)
module Dom = Graph.Dominator.Make (G)

let find_by_id id graph =
  let node =
    G.fold_vertex
      (fun n found -> if Node.id n = id then n else found)
      graph Node.empty
  in

  if node = Node.empty then
    let reason = Printf.sprintf "Cannot found node#%d" id in
    raise (NodeNotFound (id |> string_of_int, reason))
  else node

let find_in_succ cond id graph =
  let node = find_by_id id graph in
  let succ = G.succ graph node in
  try List.find cond succ
  with Not_found ->
    let reason =
      Printf.sprintf "Cannot found node that satisfy your condition"
    in
    err (NodeNotFound ("", reason))

let find_by_opcode opcode graph =
  let node =
    G.fold_vertex
      (fun n found -> if Instr.opcode (Node.instr n) = opcode then n else found)
      graph Node.empty
  in

  if node = Node.empty then
    let reason =
      Printf.sprintf "Cannot found node with opcode %s" (Opcode.to_str opcode)
    in
    raise (NodeNotFound (Opcode.to_str opcode, reason))
  else node

let is_connected start_id end_id graph =
  let rec is_connected_helper present end_id visited graph =
    let next_nodes = G.succ graph present in
    List.fold_left
      (fun (result, visited) next_node ->
        if Node.id next_node = end_id then (true, visited)
        else if List.mem next_node visited then (result, visited)
        else
          let new_visited = next_node :: visited in
          let next_result, next_visited =
            is_connected_helper next_node end_id new_visited graph
          in
          (result || next_result, next_visited))
      (false, visited) next_nodes
  in
  let start_node = find_by_id start_id graph in
  is_connected_helper start_node end_id [] graph |> fst

let true_br_of id graph =
  find_in_succ
    (fun node -> node |> Node.instr |> Instr.opcode = Opcode.IfTrue)
    id graph
  |> Node.id

let false_br_of id graph =
  find_in_succ
    (fun node -> node |> Node.instr |> Instr.opcode = Opcode.IfFalse)
    id graph
  |> Node.id

let instr_of id graph = find_by_id id graph |> Node.instr

let connect_n1_n2 edge n1 n2 graph =
  G.add_edge_e graph (find_by_id n1 graph, edge, find_by_id n2 graph)

(* parse instrction id from  *)
let parse_iid line =
  let re = Re.Pcre.regexp "#([0-9]+):" in
  try Re.Group.get (Re.exec re line) 1
  with Not_found ->
    let reason = Format.asprintf "%a" Re.pp_re re in
    err (NodeNotFound (line, reason))

let create_from graph_lines =
  let module IN = Map.Make (struct
    type t = string

    let compare = compare
  end) in
  let iid2nid =
    graph_lines
    |> List.mapi (fun addr line -> (addr, line))
    |> List.fold_left
         (fun m (addr, line) ->
           let instr_id = line |> parse_iid in
           IN.add instr_id addr m)
         IN.empty
  in

  let find_nid iid = IN.find iid iid2nid in

  let parse_innodes line =
    let grep_innodes line =
      let s = Stack.create () in
      let result, len, _ =
        String.fold_left
          (fun (result, i, finished) ch ->
            if ch = '(' || ch = '[' || ch = '<' then Stack.push ch s
            else if ch = ')' || ch = ']' || ch = '>' then
              if Utils.check_bracket_match (Stack.top s) ch then
                Stack.pop s |> ignore
              else failwith "File has weird bracket";
            if Stack.length s = 1 && Stack.top s = '(' && not finished then
              (String.cat result (String.make 1 ch), i + 1, finished)
            else if String.length result > 0 then (result, i, true)
            else (result, i + 1, false))
          ("", 0, false) line
      in
      (result, len)
    in

    let result, len = grep_innodes line in
    let result_len = String.length result in

    ( String.sub result 1 (result_len - 1)
      |> StringLabels.split_on_char ~sep:' '
      |> List.filter (fun s -> String.length s > 0)
      |> List.map (fun n -> n |> parse_iid |> find_nid),
      len + 1 )
  in

  let connect_inedges edge node in_nodes graph =
    List.fold_right
      (fun in_node graph -> connect_n1_n2 edge in_node node graph)
      in_nodes graph
  in

  let rec iid_operands_to_nid_operands operands res =
    let module Operand = Operands.Operand in
    match operands with
    | h :: t -> (
        match h with
        | Operands.Operand.Id iid ->
            iid_operands_to_nid_operands t
              ((find_nid iid |> string_of_int |> Operand.of_id) :: res)
        | v -> iid_operands_to_nid_operands t (v :: res))
    | [] -> List.rev res
  in

  graph_lines
  |> List.fold_left
       (fun g line ->
         let instr_id = line |> parse_iid in
         let node_id = instr_id |> find_nid in
         let ty, opcode, operands = line |> Instr.create_from in
         let instr =
           Instr.create ty opcode (iid_operands_to_nid_operands operands [])
         in
         let node = Node.create node_id instr in
         let value_innodes, value_end = line |> parse_innodes in
         let effect_innodes, effect_end =
           String.sub line value_end (String.length line - value_end)
           |> parse_innodes
         in
         let control_start = value_end + effect_end in
         let control_innodes, _ =
           String.sub line control_start (String.length line - control_start)
           |> parse_innodes
         in
         G.add_vertex g node
         |> connect_inedges Edge.value node_id value_innodes
         |> connect_inedges Edge.effect node_id effect_innodes
         |> connect_inedges Edge.control node_id control_innodes)
       G.empty

let create_from_ir_file ir_file =
  ir_file |> Core.In_channel.read_lines |> create_from

(** Graph Visualization *)
module Dot = Graph.Graphviz.Dot (struct
  include G

  let graph_attributes _ = []

  let default_vertex_attributes _ = []

  let vertex_name v = "\"" ^ String.escaped (Node.label v) ^ "\""

  let vertex_attributes _ = [ `Shape `Box ]

  let get_subgraph _ = None

  let default_edge_attributes _ = []

  let edge_attributes (_, e, _) = [ `Label (String.sub (Edge.to_str e) 0 1) ]
end)

let generate_graph_output name g =
  let file = open_out_bin name in
  Dot.output_graph file g
