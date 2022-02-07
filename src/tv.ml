module State = Semantics.State

let ctx = Z3utils.ctx
let validator = Z3.Solver.mk_solver ctx None

let execute program params prefix =
  let init_state = State.init params in
  let rec next program state =
    if State.is_final state then (state.retvar |> Option.get, state.retexp)
    else Semantics.apply program state prefix |> next program
  in

  next program init_state

let run before after =
  let retvar_A, retexp_A = execute before [ "3000000000000000" ] "a" in
  let retvar_B, retexp_B = execute after [ "3000000000000000" ] "b" in

  let query =
    Z3.Expr.simplify
      (Z3.Boolean.mk_and ctx
         [
           retexp_A;
           retexp_B;
           Z3.Boolean.mk_not ctx (Z3.Boolean.mk_eq ctx retvar_A retvar_B);
         ])
      None
  in
  query |> Z3.Expr.to_string |> print_endline;

  let status = Z3.Solver.check validator [ query ] in
  print_endline (status |> Z3.Solver.string_of_status)
