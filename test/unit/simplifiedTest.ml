open Helper

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

let number_to_uint32_tests =
  let name = "Simplified::NumberToUint32" in
  let msg = "\027[91m" ^ name ^ "\027[0m" in
  let number_to_uint32_eq_test actual expected =
    let eq = Value.eq in
    let expected = expected |> Uint32.of_int in
    let _ = value_eq eq actual expected in
    name >:: fun _ ->
    assert_equal ~msg ~cmp:(value_eq eq) ~printer:value_printer actual expected
  in
  let apply n = n |> apply_sem_v1m number_to_uint32 in

  [
    number_to_uint32_eq_test (apply (i32_to_i32_value 0)) 0;
    number_to_uint32_eq_test (apply (i32_to_tagged_signed 1)) 1;
    number_to_uint32_eq_test (apply ("-1.0" |> f_to_f64_value)) 4294967295;
    number_to_uint32_eq_test (apply ("-0.0" |> f_to_f64_value)) 0;
    number_to_uint32_eq_test (apply ("0.0" |> f_to_f64_value)) 0;
    number_to_uint32_eq_test (apply ("1.0" |> f_to_f64_value)) 1;
    number_to_uint32_eq_test
      (apply ("4294967295.0" |> f_to_f64_value))
      4294967295;
    number_to_uint32_eq_test (apply ("4294967297.0" |> f_to_f64_value)) 1;
    number_to_uint32_eq_test
      (apply ("-1.0" |> f_to_heap_number |> HeapNumber.to_float64))
      4294967295;
    number_to_uint32_eq_test
      (apply ("0.0" |> f_to_heap_number |> HeapNumber.to_float64))
      0;
    number_to_uint32_eq_test
      (apply ("-0.0" |> f_to_heap_number |> HeapNumber.to_float64))
      0;
    number_to_uint32_eq_test
      (apply ("1.0" |> f_to_heap_number |> HeapNumber.to_float64))
      1;
    number_to_uint32_eq_test
      (apply ("4294967295.0" |> f_to_heap_number |> HeapNumber.to_float64))
      4294967295;
    number_to_uint32_eq_test (apply (u32_to_u32_value 0)) 0;
    number_to_uint32_eq_test (apply (u32_to_u32_value 1)) 1;
    number_to_uint32_eq_test (apply (u32_to_u32_value 4294967295)) 4294967295;
  ]

let number_to_int32_tests =
  let name = "Simplified::NumberToInt32" in
  let msg = "\027[91m" ^ name ^ "\027[0m" in
  let number_to_int32_eq_test actual expected =
    let eq = Value.eq in
    let expected = Int32.of_int expected in
    let _ = value_eq eq actual expected in
    name >:: fun _ ->
    assert_equal ~msg ~cmp:(value_eq eq) ~printer:value_printer actual expected
  in
  let apply n = n |> apply_sem_v1m number_to_int32 in

  [
    number_to_int32_eq_test (apply (i32_to_i32_value 0)) 0;
    number_to_int32_eq_test (apply (i32_to_tagged_signed 1)) 1;
    number_to_int32_eq_test (apply ("-1.0" |> f_to_f64_value)) (-1);
    number_to_int32_eq_test (apply ("-0.0" |> f_to_f64_value)) 0;
    number_to_int32_eq_test (apply ("0.0" |> f_to_f64_value)) 0;
    number_to_int32_eq_test (apply ("1.0" |> f_to_f64_value)) 1;
    number_to_int32_eq_test
      (apply ("4294967295.0" |> f_to_f64_value))
      4294967295;
    number_to_int32_eq_test (apply ("4294967297.0" |> f_to_f64_value)) 1;
    number_to_int32_eq_test
      (apply ("-1.0" |> f_to_heap_number |> HeapNumber.to_float64))
      (-1);
    number_to_int32_eq_test
      (apply ("-0.0" |> f_to_heap_number |> HeapNumber.to_float64))
      0;
    number_to_int32_eq_test
      (apply ("0.0" |> f_to_heap_number |> HeapNumber.to_float64))
      0;
    number_to_int32_eq_test
      (apply ("1.0" |> f_to_heap_number |> HeapNumber.to_float64))
      1;
    number_to_int32_eq_test
      (apply ("4294967295.0" |> f_to_heap_number |> HeapNumber.to_float64))
      4294967295;
    number_to_int32_eq_test (apply (u32_to_u32_value 0)) 0;
    number_to_int32_eq_test (apply (u32_to_u32_value 1)) 1;
    number_to_int32_eq_test (apply (u32_to_u32_value 4294967295)) 4294967295;
  ]

let number_comparison op f1 f2 expected =
  let name =
    "Number::" ^ (f1 |> string_of_float) ^ op ^ (f2 |> string_of_float)
  in
  let opsem =
    match op with
    | "<" -> Simplified.number_less_than
    | "<=" -> Simplified.number_less_than_or_equal
    | ">" | ">=" | "=" -> failwith "not implemented"
    | _ -> failwith "unreachable"
  in
  let msg = "\027[91m" ^ name ^ "\027[0m" in
  let true_cst = RegisterFile.find "true" state.register_file in
  let false_cst = RegisterFile.find "false" state.register_file in
  let expected = if expected then true_cst else false_cst in
  let n1 = Float64.of_float f1 in
  let n2 = Float64.of_float f1 in
  let result =
    state |> opsem n1 n2 state.memory |> State.register_file
    |> RegisterFile.find "0"
  in
  let eq = Value.eq in
  let _ = value_eq eq result expected in
  name >:: fun _ ->
  assert_equal ~msg ~cmp:(value_eq eq) ~printer:(value_printer ~indent:1)
    expected result

let number_nan_lt_nan = number_comparison "<" nan nan false

let number_nan_le_nan = number_comparison "<=" nan nan false

let suite =
  "suite"
  >::: [
         change_int31_to_tagged_signed_pos_val;
         change_int31_to_tagged_signed_neg_val;
         number_nan_lt_nan;
       ]
       @ number_to_uint32_tests @ number_to_int32_tests

let _ = OUnit2.run_test_tt_main suite