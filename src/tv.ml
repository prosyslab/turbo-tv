module State = Semantics.State

let execute program params =
  let init_state = State.init params in
  let rec next program state =
    if State.is_final state then state.return_value
    else
      Semantics.apply program state |> next program
  in

  next program init_state

let run before after =
  let final_state_A = execute before ["3"] in
  let final_state_B = execute after ["3"] in

  if final_state_A = final_state_B then print_endline "success"
  else print_endline "fail"
