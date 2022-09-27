open Helper

let conversion_test i_ty o_ty desc input expected =
  let name = Printf.sprintf "change_%s_to_%s_%s" i_ty o_ty desc in
  let ty, eq, convert =
    match (i_ty, o_ty) with
    | "float64", "int64" -> (Type.int64, Int64.eq, change_float64_to_int64)
    | "float64", "int32" -> (Type.int32, Int32.eq, change_float64_to_int32)
    | _ -> failwith "not implemented"
  in
  let msg = "\027[91m" ^ name ^ "\027[0m" in
  let result =
    state
    |> convert (Float64.from_numeral input)
    |> State.register_file |> RegisterFile.find "0"
  in
  let expected = Value.from_int expected |> Value.cast ty in
  let _ = value_eq eq result expected in
  name >:: fun _ ->
  assert_equal ~msg ~cmp:(value_eq eq) ~printer:value_printer expected result

let change_float64_to_int64_neg_val =
  conversion_test "float64" "int64" "neg_val" (-1.0) (-1)

let change_float64_to_int64_pos_val =
  conversion_test "float64" "int64" "pos_val" 1.0 1

let change_float64_to_int32_neg_val =
  conversion_test "float64" "int32" "neg_val" (-1.0) (-1)

let change_float64_to_int32_pos_val =
  conversion_test "float64" "int32" "pos_val" 1.0 1

let change_float64_to_int32_pos_ovf =
  conversion_test "float64" "int32" "pos_ovf" 2147483648.0 (-2147483648)

let change_float64_to_int32_pos_ovf2 =
  conversion_test "float64" "int32" "pos_ovf2" 4294967295.0 (-1)

let change_float64_to_int32_pos_ovf3 =
  conversion_test "float64" "int32" "pos_ovf3" 4294967297.0 1

let change_float64_to_int32_neg_udf =
  conversion_test "float64" "int32" "neg_udf" (-2147483648.0) (-2147483648)

let change_float64_to_int32_neg_udf2 =
  conversion_test "float64" "int32" "neg_udf2" (-4294967295.0) 1

let change_float64_to_int32_neg_udf3 =
  conversion_test "float64" "int32" "neg_udf2" (-4294967297.0) (-1)

let suite =
  "Test suite for machine-level operator semantics"
  >::: [
         change_float64_to_int32_pos_val;
         change_float64_to_int32_neg_val;
         change_float64_to_int32_pos_ovf;
         change_float64_to_int32_pos_ovf2;
         change_float64_to_int32_pos_ovf3;
         change_float64_to_int32_neg_udf;
         change_float64_to_int32_neg_udf2;
         change_float64_to_int32_neg_udf3;
         change_float64_to_int64_pos_val;
         change_float64_to_int64_neg_val;
       ]

let _ = OUnit2.run_test_tt_main suite
