module Node = struct
  type address = int
  type id = int
  type t = address * id * Instr.t

  let compare = compare
  let hash = Hashtbl.hash
  let equal = ( = )
  let create address id instr : t = (address, id, instr)
  let empty = (-1, -1, Instr.empty)
  let address (address, _, _) : address = address
  let id (_, id, _) : id = id
  let instr (_, _, instr) : Instr.t = instr

  let label node =
    let _, id, instr = node in
    let opcode = instr |> Instr.opcode in
    let operands = instr |> Instr.operands in
    Printf.sprintf "#%d:%s(%s)" id (Opcode.to_str opcode)
      (Operand.str_of_operands operands)
end

module G = Graph.Persistent.Digraph.ConcreteBidirectional (Node)

exception Node_not_found of string * string
exception Invalid_graph_line of string * string

let err excpt =
  (match excpt with
  | Invalid_graph_line (c, r) ->
      Printf.fprintf stderr "Invalid graph line: %s\n%s\n\n" c r
  | Node_not_found (c, r) ->
      Printf.fprintf stderr "Node not found: %s\n%s\n\n" c r
  | _ -> ());
  raise excpt

let find_node id graph =
  let node =
    G.fold_vertex
      (fun n found -> if Node.id n = id then n else found)
      graph Node.empty
  in

  if node = Node.empty then
    err
      (Node_not_found
         (id |> string_of_int, Printf.sprintf "Cannot found node#%d" id))
  else node

let connect_n1_n2 n1 n2 graph =
  G.add_edge graph (find_node n1 graph) (find_node n2 graph)

let parse_id line =
  let re = Re.Pcre.regexp "#([0-9]+):" in
  try Re.Group.get (Re.exec re line) 1 |> int_of_string
  with Not_found ->
    let reason = Format.asprintf "Printf.sprintf %a" Re.pp_re re in
    err (Node_not_found (line, reason))

let create_from graph_lines =
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
    |> List.map (fun n -> parse_id n)
  in

  let connect_inedges node in_nodes graph =
    List.fold_right
      (fun in_node graph -> connect_n1_n2 in_node node graph)
      in_nodes graph
  in

  let graph = G.empty in
  graph_lines
  |> List.mapi (fun i line -> (i, line))
  |> List.fold_left
       (fun g (i, line) ->
         let id = line |> parse_id in
         let instr = line |> Instr.create_from in
         let node = Node.create i id instr in
         let in_nodes = line |> parse_innodes in
         G.add_vertex g node |> connect_inedges id in_nodes)
       graph

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
