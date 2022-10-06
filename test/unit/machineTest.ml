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
    |> convert (Float64.of_float input)
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

let word_logical_shift_test desc width kind li ri expected =
  let name = Printf.sprintf "word%d%s_%s" width kind desc in
  let msg = "\027[91m" ^ name ^ "\027[0m" in
  let op =
    match (width, kind) with
    | 32, "shl" -> word32_shl
    | 32, "shr" -> word32_shr
    | 8, _ | 16, _ | 64, _ -> failwith "not implemented"
    | _ -> failwith "unreachable"
  in
  let eq, lval, rval =
    match width with
    | 32 -> (Word32.eq, Int32.of_int li, Int32.of_int ri)
    | 8 | 16 | 64 -> failwith "not implemented"
    | _ -> failwith "unreachable"
  in

  let result =
    state |> op lval rval |> State.register_file |> RegisterFile.find "0"
  in
  let expected = Value.from_int expected |> Value.cast Type.int64 in
  let _ = value_eq eq result expected in
  name >:: fun _ ->
  assert_equal ~msg ~cmp:(value_eq Int64.eq) ~printer:value_printer expected
    result

let word32_shr_mod32_off =
  word_logical_shift_test "mod32_off" 32 "shr" (-2147483648) (-1073741808) 32768

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
         word32_shr_mod32_off;
       ]

let _ = OUnit2.run_test_tt_main suite
