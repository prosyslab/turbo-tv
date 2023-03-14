open Z3utils
module G = IR.G

let read_opcodes = [ Opcode.Load; Opcode.LoadElement; Opcode.LoadField ]

let write_opcodes = [ Opcode.Store; Opcode.StoreElement; Opcode.StoreField ]

let find_candids (pgr : G.t) =
  let read_nodes =
    pgr
    |> IR.find_all_nodes (fun n ->
           let opcode = Instr.opcode (IR.Node.instr n) in
           List.fold_left (fun acc op -> acc || opcode = op) false read_opcodes)
  in
  let write_nodes =
    pgr
    |> IR.find_all_nodes (fun n ->
           let opcode = Instr.opcode (IR.Node.instr n) in
           List.fold_left (fun acc op -> acc || opcode = op) false write_opcodes)
  in
  let cfg = IR.get_control_flow_graph pgr in

  let least_ctrl_dom_of_n1_n2 n1 n2 =
    let n1_dom = IR.dominators cfg n1 in
    let n2_dom = IR.dominators cfg n2 in
    List.filter (fun n -> List.mem n n2_dom) n1_dom |> List.rev |> List.hd
  in

  let has_order n1 n2 =
    let n1_id = IR.Node.id n1 in
    let n2_id = IR.Node.id n2 in
    IR.is_connected n1_id n2_id pgr || IR.is_connected n2_id n1_id pgr
  in

  let rec aux res nodes =
    match nodes with
    | [] -> res
    | n1 :: rest ->
        let res =
          List.fold_left
            (fun res n2 ->
              if
                not
                  (least_ctrl_dom_of_n1_n2 n1 n2
                   |> IR.Node.instr |> Instr.opcode = Opcode.Branch
                  || has_order n1 n2)
              then (n1 |> IR.Node.id, n2 |> IR.Node.id) :: res
              else res)
            res rest
        in
        aux res rest
  in
  aux [] (read_nodes @ write_nodes)

let can_be_overlapped boundaries candid =
  let m, n = candid in
  let {
    State.AccessInfo.bid = m_bid;
    is_read = _m_read;
    lower = m_lb;
    upper = m_ub;
  } =
    State.AccessInfo.find m boundaries
  in
  let {
    State.AccessInfo.bid = n_bid;
    is_read = _n_read;
    lower = n_lb;
    upper = n_ub;
  } =
    State.AccessInfo.find n boundaries
  in
  Bool.ands
    [
      Bool.eq m_bid n_bid;
      Bool.ors
        [
          (* m_lb - n_lb - m_ub - n_ub *)
          Bool.ands
            [
              BitVec.uleb m_lb n_lb;
              BitVec.uleb m_ub n_ub;
              BitVec.uleb n_lb m_ub;
            ];
          (* n_lb - m_lb - n_ub - m_ub *)
          Bool.ands
            [
              BitVec.uleb n_lb m_lb;
              BitVec.uleb n_ub m_ub;
              BitVec.uleb m_lb n_ub;
            ];
          (* n_lb - m_lb - m_ub - n_ub *)
          Bool.ands [ BitVec.uleb n_lb m_lb; BitVec.uleb m_ub n_ub ];
          (* m_lb - n_lb - n_ub - m_ub *)
          Bool.ands [ BitVec.uleb m_lb n_lb; BitVec.uleb n_ub m_ub ];
        ];
    ]
