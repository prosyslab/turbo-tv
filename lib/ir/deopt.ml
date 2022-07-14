open Control
open Err
open Z3utils

module DeoptFile = struct
  module D = Map.Make (String)

  let prefix = ref ""

  let did id = !prefix ^ id

  let init stage =
    prefix := String.sub stage 0 1 ^ "u";
    D.empty

  let add key value uf = D.add key value uf

  let find uid uf =
    let uid = !prefix ^ uid in
    try D.find uid uf
    with Not_found ->
      let cause = uid in
      let reason = Format.sprintf "Cannot find %s from DeoptFile" cause in
      err (IdNotFound (cause, reason))

  let find_all uids cf = List.map (fun uid -> find uid cf) uids

  let empty = D.empty

  let iter = D.iter
end

let propagate program (opcode : Opcode.t) operands cf df deopt =
  let deopt_from_input =
    match opcode with
    | Merge ->
        let pids = operands |> Operands.id_of_all in
        let conds = ControlFile.find_all pids cf in
        let deopts = DeoptFile.find_all pids df in
        Bool.ors
          (List.rev_map2
             (fun cond deopt -> Bool.ands [ cond; deopt ])
             conds deopts)
    | Phi -> (
        let rev = operands |> List.rev in
        let ctrl_id = Operands.id_of_nth rev 0 in
        let ctrl_deopt = DeoptFile.find ctrl_id df in
        let _, ctrl_opcode, incomings_id =
          IR.instr_of (ctrl_id |> int_of_string) program
        in
        match ctrl_opcode with
        | Merge ->
            let incoming_ctrl_tokens =
              ControlFile.find_all (incomings_id |> Operands.id_of_all) cf
            in
            let incoming_deopts =
              DeoptFile.find_all
                (rev |> List.tl |> List.tl |> List.rev |> Operands.id_of_all)
                df
            in
            Bool.ors
              (ctrl_deopt
              :: List.rev_map2
                   (fun ctrl deopt -> Bool.ands [ ctrl; deopt ])
                   incoming_ctrl_tokens incoming_deopts)
        | Dead -> Bool.tr
        | _ ->
            failwith
              (Format.sprintf "Phi is not implemented for incoming opcode: %s"
                 (ctrl_opcode |> Opcode.to_str)))
    | _ ->
        let pids = Operands.id_of_all operands in
        let deopts = DeoptFile.find_all pids df in
        Bool.ors deopts
  in
  Bool.ors [ deopt; deopt_from_input ]
