module State = Semantics.State
module Params = Semantics.Params
open Z3utils

let ctx = Z3utils.ctx
let validator = Solver.init

(* execute the program and retrieve a final state *)
let execute program nparams prefix =
  let rec next program state =
    if State.is_final state then (state.retvar |> Option.get, state.assertion)
    else Semantics.apply program state prefix |> next program
  in

  (* symbols for parameters *)
  let init_state = State.init nparams in
  next program init_state

let run nparams before after =
  let retvar_A, assertion_A = execute before nparams "b" in
  let retvar_B, assertion_B = execute after nparams "a" in

  let assertion =
    Bool.ands [ assertion_A; assertion_B; Bool.neq retvar_A retvar_B ]
  in
  let assertion_str = assertion |> str_of_simplified in

  let status = Solver.check validator assertion in

  match status with
  | SATISFIABLE ->
      let model = Option.get (Solver.get_model validator) in
      let model_str = model |> Model.to_str in

      Printf.printf "X -> \n";
      Printf.printf "Assertion: \n%s\n" assertion_str;
      Printf.printf "Model: \n%s" model_str
  | UNSATISFIABLE ->
      Printf.printf "O -> \n";
      Printf.printf "Assertion: \n%s" assertion_str
  | _ -> failwith "unknown"
