open Z3utils
module Node = IR.Node
module G = IR.G

let set_assertion program state =
  G.fold_vertex
    (fun (pc, (_, opcode, _)) state ->
      let pc = pc |> string_of_int in
      match opcode with
      | LoadField ->
          let is_angelic = AngelicFile.find pc state.State.is_angelic_value in
          let value = RegisterFile.find pc state.State.register_file in
          let assertion =
            Bool.implies
              (Bool.ands
                 [
                   is_angelic;
                   BitVec.eqb (Value.ty_of value) Type.tagged_pointer;
                 ])
              (value |> Memory.is_angelic state.State.memory)
          in
          {
            state with
            assertion = Bool.ands [ state.State.assertion; assertion ];
          }
      | _ -> state)
    program state
