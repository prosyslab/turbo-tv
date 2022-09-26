open Lib
open Lib.Z3utils
open Lib.Simplified
open Lib.ValueOperator
open OUnit2

let state = State.init 0 "test"

let solver = Solver.init None

let is_satisfiable expr =
  match Solver.check solver expr with
  | Z3.Solver.SATISFIABLE -> true
  | _ -> false

let value_eq eq e1 e2 = eq e1 e2 |> is_satisfiable

let value_printer e =
  let model = Solver.get_model solver |> Option.get in
  Format.sprintf "Formated: %s\nRaw: %s"
    (e |> Printer.value_to_string model state.register_file state.memory)
    (e |> Expr.to_simplified_string)

let change_int31_to_tagged_signed desc input expected =
  let name = String.concat "_" [ "change_int31_to_tagged_signed"; desc ] in
  let result =
    state
    |> change_int31_to_tagged_signed
         (Value.from_int input |> Value.cast Type.int32)
    |> State.register_file |> RegisterFile.find "0"
  in
  let expected =
    Value.from_int expected |> Value.cast Type.int32 |> Int32.to_tagged_signed
  in
  let eq = TaggedSigned.eq in
  name >:: fun _ ->
  assert_equal ~msg:name ~cmp:(value_eq eq) ~printer:value_printer result
    expected

let change_int31_to_tagged_signed_pos_val =
  change_int31_to_tagged_signed "pos_val" 0 0

let change_int31_to_tagged_signed_neg_val =
  change_int31_to_tagged_signed "neg_val" (-1) (-1)

let number_to ty_s desc input expected =
  let name = String.concat "_" [ "number_to"; ty_s; desc ] in
  let ty, eq, convert =
    match ty_s with
    | "int32" -> (Type.int32, Int32.eq, number_to_int32)
    | "uint32" -> (Type.uint32, Uint32.eq, number_to_uint32)
    | _ -> failwith "unreachable"
  in
  let result =
    state
    |> convert (Float64.from_numeral input) state.memory
    |> State.register_file |> RegisterFile.find "0"
  in
  let expected = Value.from_int expected |> Value.cast ty in
  let _ = value_eq eq result expected in
  name >:: fun _ ->
  assert_equal ~msg:name ~cmp:(value_eq eq) ~printer:value_printer result
    expected

let number_to_uint32_neg_val = number_to "uint32" "neg_val" (-1.0) 4294967295

let number_to_uint32_pos_val = number_to "uint32" "pos_val" 1.0 1

let number_to_uint32_neg_ovf =
  number_to "uint32" "neg_ovf" (-4294967297.0) 4294967295

let number_to_uint32_pos_ovf = number_to "uint32" "pos_ovf" 4294967297.0 1

let number_to_int32_neg_val = number_to "int32" "neg_val" (-1.0) (-1)

let number_to_int32_pos_val = number_to "int32" "pos_val" 1.0 1

let number_to_int32_neg_ovf = number_to "int32" "neg_ovf" (-4294967297.0) (-1)

let number_to_int32_pos_ovf = number_to "int32" "pos_ovf" 4294967297.0 1

let suite =
  "suite"
  >::: [
         change_int31_to_tagged_signed_pos_val;
         change_int31_to_tagged_signed_neg_val;
         number_to_uint32_neg_val;
         number_to_uint32_pos_val;
         number_to_uint32_neg_ovf;
         number_to_uint32_pos_ovf;
         number_to_int32_neg_val;
         number_to_int32_pos_val;
         number_to_int32_neg_ovf;
         number_to_int32_pos_ovf;
       ]

let _ = OUnit2.run_test_tt_main suite