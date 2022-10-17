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

let number_to ty_s desc input expected =
  let name = String.concat "_" [ "number_to"; ty_s; desc ] in
  let ty, eq, convert =
    match ty_s with
    | "int32" -> (Type.int32, Int32.eq, number_to_int32)
    | "uint32" -> (Type.uint32, Uint32.eq, number_to_uint32)
    | _ -> failwith "not implemented"
  in
  let msg = "\027[91m" ^ name ^ "\027[0m" in
  let expected = Value.from_int expected |> Value.cast ty in
  let result =
    state
    |> convert (Float64.of_float input) state.memory
    |> State.register_file |> RegisterFile.find "0"
  in
  let _ = value_eq eq result expected in
  name >:: fun _ ->
  assert_equal ~msg ~cmp:(value_eq eq) ~printer:value_printer expected result

let number_to_uint32_neg_val = number_to "uint32" "neg_val" (-1.0) 4294967295

let number_to_uint32_pos_val = number_to "uint32" "pos_val" 1.0 1

let number_to_uint32_neg_ovf =
  number_to "uint32" "neg_ovf" (-4294967297.0) 4294967295

let number_to_uint32_pos_ovf = number_to "uint32" "pos_ovf" 4294967297.0 1

let number_to_int32_neg_val = number_to "int32" "neg_val" (-1.0) (-1)

let number_to_int32_pos_val = number_to "int32" "pos_val" 1.0 1

let number_to_int32_neg_ovf = number_to "int32" "neg_ovf" (-4294967297.0) (-1)

let number_to_int32_pos_ovf = number_to "int32" "pos_ovf" 4294967297.0 1

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
  let expected = if expected then Value.tr else Value.fl in
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
         number_to_uint32_neg_val;
         number_to_uint32_pos_val;
         number_to_uint32_neg_ovf;
         number_to_uint32_pos_ovf;
         number_to_int32_neg_val;
         number_to_int32_pos_val;
         number_to_int32_neg_ovf;
         number_to_int32_pos_ovf;
         number_nan_lt_nan;
       ]

let _ = OUnit2.run_test_tt_main suite