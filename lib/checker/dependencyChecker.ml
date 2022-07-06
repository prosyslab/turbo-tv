open Z3utils

let deopt_nodes : Opcode.t list = [ Deoptimize; DeoptimizeIf; DeoptimizeUnless ]

let kill_nodes : Opcode.t list = [ Throw ]

module NodeMap = Map.Make (Int)

let validator =
  let tactic = Tactic.and_then [ "simplify"; "fpa2bv"; "qfaufbv" ] in
  Solver.init_with_tactic tactic

let deopt_node_map_add key (opcode : Opcode.t) operands rf control m =
  let cond =
    match opcode with
    | Deoptimize -> control
    | DeoptimizeIf ->
        let cid = Operands.id_of_nth operands 0 in
        let c = RegisterFile.find cid rf in
        Bool.ands [ control; Value.eq c Value.tr ]
    | DeoptimizeUnless ->
        let cid = Operands.id_of_nth operands 0 in
        let c = RegisterFile.find cid rf in
        Bool.ands [ control; Value.eq c Value.fl ]
    | _ ->
        failwith (Printf.sprintf "%s is not deopt node" (Opcode.to_str opcode))
  in
  NodeMap.add key cond m

let report desc result =
  let output = if result then "Verified" else "Not Verified" in
  Printf.printf "Dependency check for %s: %s\n" desc output

let is_dependency_exist deopt_node_map_id kill_node_map_id graph =
  IR.is_connected deopt_node_map_id kill_node_map_id graph
  || IR.is_connected kill_node_map_id deopt_node_map_id graph

let check program deopt_node_map kill_node_map assertion desc =
  NodeMap.fold
    (fun deopt_node_map_id deopt_node_map_cond result ->
      NodeMap.fold
        (fun kill_node_map_id kill_node_map_cond result ->
          let cond =
            Bool.ands [ assertion; deopt_node_map_cond; kill_node_map_cond ]
          in
          match Solver.check validator cond with
          | SATISFIABLE ->
              if is_dependency_exist deopt_node_map_id kill_node_map_id program
              then result
              else false
          | UNSATISFIABLE -> result
          | _ -> failwith "dependency check fails with known status")
        kill_node_map result)
    deopt_node_map true
  |> report desc