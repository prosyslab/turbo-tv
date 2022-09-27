open Helper

let conversion_test i_ty o_ty desc input expected =
  let name = Printf.sprintf "change_%s_to_%s_%s" i_ty o_ty desc in
  let ty, eq, convert =
    match (i_ty, o_ty) with
    | "float64", "int64" -> (Type.int64, Int64.eq, change_float64_to_int64)
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

let suite =
  "Test suite for machine-level operator semantics"
  >::: [ change_float64_to_int64_pos_val; change_float64_to_int64_neg_val ]

let _ = OUnit2.run_test_tt_main suite
