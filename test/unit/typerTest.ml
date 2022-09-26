open Lib
open Lib.Z3utils
open Lib.ValueOperator
open OUnit2

let expr_printer b = b |> Expr.to_simplified_string

let solver = Solver.init None

let is_satisfiable expr =
  match Solver.check solver expr with
  | Z3.Solver.SATISFIABLE -> true
  | _ -> false

let mz_is_mz =
  "mz_is_mz" >:: fun _ ->
  assert_bool "mz_is_mz"
    (is_satisfiable
       (Typer.verify Float64.minus_zero Types.MinusZero (Memory.init 0)))

let nan_is_nan =
  "nan_is_nan" >:: fun _ ->
  assert_bool "nan_is_nan"
    (is_satisfiable (Typer.verify Float64.nan Types.NaN (Memory.init 0)))

let simple_union =
  "mz_is_u32_or_mz" >:: fun _ ->
  assert_bool "mz_is_u32_or_mz"
    (is_satisfiable
       (Typer.verify Float64.minus_zero
          (Types.Union [ Types.MinusZero; Types.Unsigned32 ])
          (Memory.init 0)))

let suite = "suite" >::: [ mz_is_mz; nan_is_nan; simple_union ]

let _ = OUnit2.run_test_tt_main suite