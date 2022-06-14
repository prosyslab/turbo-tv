module Operand = Operands.Operand

type bracket_operands_env = {
  token : string;
  operands : Operand.t list;
  bracket_stack : char Stack.t;
  started : bool;
}

let bracket_operands_parse instr =
  let empty_stack = Stack.create () in
  let init_env =
    { token = ""; operands = []; bracket_stack = empty_stack; started = false }
  in
  let result =
    String.fold_left
      (fun env ch ->
        if env.started && Stack.is_empty env.bracket_stack then env
        else
          match ch with
          | '(' | '[' | '<' ->
              Stack.push ch env.bracket_stack;
              if ch = '[' && not env.started then { env with started = true }
              else env
          | ')' | ']' | '>' ->
              let left = Stack.pop env.bracket_stack in
              if not (Utils.check_bracket_match left ch) then
                failwith (Printf.sprintf "Bracket mismatch: %c %c" left ch);
              if ch = ']' && Stack.is_empty env.bracket_stack then
                let operand = env.token |> Operand.of_const in
                { env with token = ""; operands = operand :: env.operands }
              else env
          | ',' ->
              if Stack.length env.bracket_stack = 1 then
                let operand = env.token |> Operand.of_const in
                { env with token = ""; operands = operand :: env.operands }
              else
                let token = env.token ^ String.make 1 ch in
                { env with token }
          | ' ' ->
              if String.length env.token = 0 then env
              else
                let token = env.token ^ String.make 1 ch in
                { env with token }
          | _ ->
              if not env.started then env
              else
                let token = env.token ^ String.make 1 ch in
                { env with token })
      init_env instr
  in
  List.rev result.operands