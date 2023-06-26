(* Unit test of Number module *)
open Helper

(* IsNumber: Number x Number -> Z3.Bool *)
let is_number_tests =
  let name = "Number::IsNumber" in
  let msg = "\027[91m" ^ name ^ "\027[0m" in
  let is_number_eq_test num expected =
    let state = Common.number_constant num state in
    let num_v = RegisterFile.find "0" state.register_file in
    let actual = Number.is_number num_v state.memory in
    let expected = if expected then Bool.tr else Bool.fl in
    let eq = Bool.eq in
    let _ = value_eq eq actual expected in
    name >:: fun _ ->
    assert_equal ~msg ~cmp:(value_eq eq) ~printer:(bool_printer ~indent:1)
      actual expected
  in
  [ is_number_eq_test "1" true; is_number_eq_test "nan" true ]

let suite = "suite" >::: is_number_tests

let _ = OUnit2.run_test_tt_main suite
