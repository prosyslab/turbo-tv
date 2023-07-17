open Z3utils
module Node = IR.Node
module G = IR.G

let set_assertion program state =
  G.fold_vertex
    (fun (pc, (_, opcode, operands)) state ->
      let pc = pc |> string_of_int in
      let is_angelic_value = AngelicFile.find pc state.State.is_angelic_value in
      let value = RegisterFile.find pc state.State.register_file in
      let control = ControlFile.find pc state.State.control_file in
      let mem = state.State.memory in
      let assertion =
        match opcode with
        | Call ->
            let fname = Operands.const_of_nth operands 0 in
            let args_regexp =
              Re.Pcre.regexp
                "[a-zA-Z0-9:_- ]*r([0-9]+)s[0-9]+i([0-9]+)f([0-9]+)"
            in
            let n_return =
              Re.Group.get (Re.exec args_regexp fname) 1 |> int_of_string
            in
            Bool.implies control
              (if n_return = 1 then
               Bool.implies
                 (value |> Value.has_type Type.tagged_pointer)
                 (value |> Memory.is_angelic mem)
              else
                Bool.ands
                  (value |> ValueOperator.Composed.to_list
                  |> List.map (fun v ->
                         Bool.implies
                           (v |> Value.has_type Type.tagged_pointer)
                           (v |> Memory.is_angelic mem))))
        | _ ->
            Bool.implies
              (Bool.ands
                 [
                   is_angelic_value; value |> Value.has_type Type.tagged_pointer;
                 ])
              (value |> Memory.is_angelic state.State.memory)
      in
      State.update ~assertion state)
    program state
