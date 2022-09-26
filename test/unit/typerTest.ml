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

let is_unsatisfiable expr =
  match Solver.check solver expr with
  | Z3.Solver.UNSATISFIABLE -> true
  | _ -> false

let mz_is_mz =
  "mz_is_mz" >:: fun _ ->
  assert_bool "mz_is_mz"
    (is_satisfiable
       (Typer.verify Float64.minus_zero Types.MinusZero (Memory.init 0)))

let mz_is_not_signed31 =
  "mz_is_not_signed31" >:: fun _ ->
  assert_bool "mz_is_not_signed31"
    (is_unsatisfiable
       (Typer.verify Float64.minus_zero Types.Signed31 (Memory.init 0)))

let nan_is_nan =
  "nan_is_nan" >:: fun _ ->
  assert_bool "nan_is_nan"
    (is_satisfiable (Typer.verify Float64.nan Types.NaN (Memory.init 0)))

let nan_is_not_unsigned32 =
  "nan_is_not_unsigned32" >:: fun _ ->
  assert_bool "nan_is_not_unsigned32"
    (is_unsatisfiable
       (Typer.verify Float64.nan Types.Unsigned32 (Memory.init 0)))

let mz_is_u32_or_mz =
  "mz_is_u32_or_mz" >:: fun _ ->
  assert_bool "mz_is_u32_or_mz"
    (is_satisfiable
       (Typer.verify Float64.minus_zero
          (Types.Union [ Types.MinusZero; Types.Unsigned32 ])
          (Memory.init 0)))

let mz_is_not_u32_or_nan =
  "mz_is_not_u32_or_nan" >:: fun _ ->
  assert_bool "mz_is_not_u32_or_nan"
    (is_unsatisfiable
       (Typer.verify Float64.minus_zero
          (Types.Union [ Types.NaN; Types.Unsigned32 ])
          (Memory.init 0)))

let simple_in_range =
  "3.5_in_(-100,100)" >:: fun _ ->
  assert_bool "3.5_in_(-100,100)"
    (is_satisfiable
       (Typer.verify (Float64.from_numeral 3.5)
          (Types.Range (-100., 100.))
          (Memory.init 0)))

let simple_not_in_range =
  "3.5_not_in_(1.5,2.5)" >:: fun _ ->
  assert_bool "3.5_not_in_(1.5,2.5)"
    (is_unsatisfiable
       (Typer.verify (Float64.from_numeral 3.5)
          (Types.Range (1.5, 2.5))
          (Memory.init 0)))

let suite =
  "suite"
  >::: [
         mz_is_mz;
         mz_is_not_signed31;
         nan_is_nan;
         nan_is_not_unsigned32;
         mz_is_u32_or_mz;
         mz_is_not_u32_or_nan;
         simple_in_range;
         simple_not_in_range;
       ]

let _ = OUnit2.run_test_tt_main suite