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

module G = Graph.Persistent.Digraph.ConcreteBidirectional (Node)

let find_by_id id graph =
  let node =
    G.fold_vertex
      (fun n found -> if Node.id n = id then n else found)
      graph Node.empty
  in

  if node = Node.empty then
    let reason = Printf.sprintf "Cannot found node#%d" id in
    err (NodeNotFound (id |> string_of_int, reason))
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

let connect_n1_n2 n1 n2 graph =
  G.add_edge graph (find_by_id n1 graph) (find_by_id n2 graph)

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
    |> StringLabels.split_on_char ~sep:' '
    |> List.filter (fun s -> String.length s > 0)
    |> List.map (fun n -> n |> parse_iid |> find_nid)
  in

  let connect_inedges node in_nodes graph =
    List.fold_right
      (fun in_node graph -> connect_n1_n2 in_node node graph)
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
         let in_nodes = line |> parse_innodes in
         G.add_vertex g node |> connect_inedges node_id in_nodes)
       G.empty

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
