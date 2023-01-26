module Operand = Operands.Operand

type bracket_operands_env = {
  token : string;
  operands : Operand.t list;
  string_match : int;
  string_len : int;
  bracket_stack : char Stack.t;
  started : bool;
}

let bracket_operands_parse instr =
  let empty_stack = Stack.create () in
  let init_env =
    {
      token = "";
      operands = [];
      string_match = 0;
      string_len = 0;
      bracket_stack = empty_stack;
      started = false;
    }
  in
  Format.printf "instr: %s\n" instr;
  let result =
    String.fold_left
      (fun env ch ->
        if env.started && Stack.is_empty env.bracket_stack then env
        else if env.string_match <> 9 then
          match ch with
          | '(' | '[' | '<' ->
              Stack.push ch env.bracket_stack;
              if ch = '[' && not env.started then { env with started = true }
              else if ch = '[' && env.string_match = 6 then
                let token = env.token ^ String.make 1 ch in
                { env with token; string_match = 7 }
              else
                let token = env.token ^ String.make 1 ch in
                { env with token }
          | ')' | ']' | '>' ->
              let left = Stack.pop env.bracket_stack in
              if not (Utils.check_bracket_match left ch) then
                failwith (Printf.sprintf "Bracket mismatch: %c %c" left ch);
              if ch = ']' && env.string_match = 7 then
                let token = env.token ^ String.make 1 ch in
                { env with token; string_match = 8 }
              else if ch = ']' && Stack.is_empty env.bracket_stack then
                let operand = env.token |> Operand.of_const in
                { env with token = ""; operands = operand :: env.operands }
              else
                let token = env.token ^ String.make 1 ch in
                { env with token }
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
                let env =
                  match ch with
                  | 'S' when env.string_match = 0 ->
                      { env with string_match = 1 }
                  | 't' when env.string_match = 1 ->
                      { env with string_match = 2 }
                  | 'r' when env.string_match = 2 ->
                      { env with string_match = 3 }
                  | 'i' when env.string_match = 3 ->
                      { env with string_match = 4 }
                  | 'n' when env.string_match = 4 ->
                      { env with string_match = 5 }
                  | 'g' when env.string_match = 5 ->
                      { env with string_match = 6 }
                  | ('0' | '1' | '2' | '3' | '4' | '5' | '6' | '7' | '8' | '9')
                    when env.string_match = 7 ->
                      let string_len =
                        (env.string_len * 10) + int_of_char ch - int_of_char '0'
                      in
                      { env with string_len }
                  | '#' when env.string_match = 8 ->
                      { env with string_match = 9 }
                  | _ when env.string_match = 8 -> env
                  | _ -> { env with string_match = 0; string_len = 0 }
                in
                let token = env.token ^ String.make 1 ch in
                { env with token }
        else
          let token = env.token ^ String.make 1 ch in
          if env.string_len = 1 then { env with token; string_match = 0 }
          else { env with token; string_len = env.string_len - 1 })
      init_env instr
  in
  let result = List.rev result.operands in
  Format.printf "operands: \n";
  Format.print_flush ();
  List.iter (fun op -> op |> Operand.to_str |> print_endline) result;
  result
