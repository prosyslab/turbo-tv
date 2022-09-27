include Lib
include Z3utils
include Simplified
include Machine
include Common
include ValueOperator
include OUnit2

let state = State.init 0 "test"

let solver = Z3utils.Solver.init None

let is_satisfiable expr =
  match Z3utils.Solver.check solver expr with
  | Z3.Solver.SATISFIABLE -> true
  | _ -> false

let value_eq eq e1 e2 = eq e1 e2 |> is_satisfiable

let value_printer e =
  let model = Z3utils.Solver.get_model solver |> Option.get in
  Format.sprintf "\nFormatted: %s\nRaw: %s\n"
    (e |> Printer.value_to_string model state.register_file state.memory)
    (e |> Z3utils.Expr.to_simplified_string)