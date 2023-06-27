(* Unit test of Number module *)
open Helper

(* Number ::= TaggedSigned | HeapNumber | Int32 | Uint32 | Float64 *)
(* IsNumber: Number -> Z3.Bool *)
let is_number_tests =
  let name = "Number::IsNumber" in
  let msg = "\027[91m" ^ name ^ "\027[0m" in
  let is_number_eq_test num expected =
    let actual = Number.is_number num state.memory in
    let expected = if expected then Bool.tr else Bool.fl in
    let eq = Bool.eq in
    let _ = value_eq eq actual expected in
    name >:: fun _ ->
    assert_equal ~msg ~cmp:(value_eq eq) ~printer:(bool_printer ~indent:1)
      actual expected
  in
  let is_number_heap_number_ptr_eq_test (num, mem) expected =
    let actual = Number.is_number num mem in
    let expected = if expected then Bool.tr else Bool.fl in
    let eq = Bool.eq in
    let _ = value_eq eq actual expected in
    name >:: fun _ ->
    assert_equal ~msg ~cmp:(value_eq eq) ~printer:(bool_printer ~indent:1)
      actual expected
  in
  [
    is_number_eq_test (mk_tagged_signed 1) true;
    is_number_eq_test (mk_tagged_signed 0) true;
    is_number_heap_number_ptr_eq_test (mk_heap_number_ptr nan) true;
    is_number_heap_number_ptr_eq_test (mk_heap_number_ptr infinity) true;
    is_number_heap_number_ptr_eq_test (mk_heap_number_ptr 1.0e10) true;
    is_number_heap_number_ptr_eq_test (mk_heap_number_ptr (-0.0)) true;
    is_number_eq_test (mk_int32 1) true;
    is_number_eq_test (mk_int32 0) true;
    is_number_eq_test (mk_uint32 0) true;
    is_number_eq_test (mk_uint32 1) true;
    is_number_eq_test (mk_float64 nan) true;
    is_number_eq_test (mk_float64 infinity) true;
    is_number_eq_test (mk_float64 1.0e10) true;
    is_number_eq_test (mk_float64 (-0.0)) true;
    is_number_eq_test false_cst false;
    is_number_eq_test true_cst false;
    is_number_eq_test null_cst false;
    is_number_eq_test undefined_cst false;
    is_number_eq_test (mk_int64 (-1)) false;
    is_number_eq_test (mk_int64 0) false;
  ]

(* IsNumber: Number x Number -> Bool *)
let number_equal_tests =
  let name = "Number::Equal" in
  let msg = "\027[91m" ^ name ^ "\027[0m" in
  let number_equal_eq_test num1 num2 expected =
    let actual = Number.equal num1 num2 state.memory in
    let expected = if expected then Value.tr else Value.fl in
    let eq = Bool.eq in
    let _ = value_eq eq actual expected in
    name >:: fun _ ->
    assert_equal ~msg ~cmp:(value_eq eq) ~printer:(bool_printer ~indent:1)
      actual expected
  in
  [
    number_equal_eq_test (mk_tagged_signed 1) (mk_tagged_signed 1) true;
    number_equal_eq_test (mk_tagged_signed 1) (mk_tagged_signed 0) false;
    number_equal_eq_test (mk_int32 1) (mk_int32 1) true;
    number_equal_eq_test (mk_int32 1) (mk_int32 0) false;
    number_equal_eq_test (mk_float64 nan) (mk_float64 (-0.0)) false;
    number_equal_eq_test (mk_float64 0.0) (mk_float64 nan) false;
    number_equal_eq_test (mk_float64 nan) (mk_float64 nan) false;
    number_equal_eq_test (mk_float64 2.0) (mk_float64 2.0) true;
    number_equal_eq_test (mk_float64 0.0) (mk_float64 (-0.0)) true;
    number_equal_eq_test (mk_float64 (-0.0)) (mk_float64 0.0) true;
    number_equal_eq_test (mk_tagged_signed 0) (mk_float64 0.0) true;
    number_equal_eq_test (mk_tagged_signed 0) (mk_float64 (-0.0)) true;
    number_equal_eq_test (mk_tagged_signed 1) (mk_int32 1) true;
    number_equal_eq_test (mk_tagged_signed 2) (mk_int32 1) false;
    number_equal_eq_test (mk_tagged_signed 2) (mk_float64 2.0) true;
    number_equal_eq_test (mk_tagged_signed 2) (mk_float64 2.1) false;
    number_equal_eq_test (mk_tagged_signed (-1)) (mk_int32 (-1)) true;
    number_equal_eq_test (mk_tagged_signed (-1)) (mk_float64 (-1.0)) true;
    number_equal_eq_test (mk_tagged_signed (-1)) (mk_uint32 4294967295) false;
    number_equal_eq_test
      (mk_tagged_signed (-1073741824))
      (mk_tagged_signed 0) false;
  ]

let suite = "suite" >::: is_number_tests @ number_equal_tests

let _ = OUnit2.run_test_tt_main suite
