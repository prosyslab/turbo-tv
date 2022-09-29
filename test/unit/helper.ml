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

let is_unsatisfiable expr =
  match Solver.check solver expr with
  | Z3.Solver.UNSATISFIABLE -> true
  | _ -> false

let value_eq eq e1 e2 = eq e1 e2 |> is_satisfiable

let repeat s n =
  let rec helper s1 n1 = if n1 = 0 then s1 else helper (s1 ^ s) (n1 - 1) in
  helper "" n

let value_printer ?(indent = 0) e =
  let model = Z3utils.Solver.get_model solver |> Option.get in
  let indent = repeat "  " indent in
  String.concat "\n"
    [
      Format.sprintf "%sFormatted: %s" indent
        (e |> Printer.value_to_string model state.register_file state.memory);
      Format.sprintf "%sRaw: %s" indent (e |> Expr.to_simplified_string);
    ]
