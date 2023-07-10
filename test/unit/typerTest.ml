open Helper

let printer = Expr.to_simplified_string

let check desc value ty expected =
  let type_is_verified = Typer.verify value ty state.memory in
  let eq = Bool.eq in
  let _ = value_eq eq type_is_verified expected in
  let msg =
    Format.sprintf "[%s]\nValue:\n%s\nType: %s\n" desc
      (value |> value_printer ~indent:1)
      (ty |> Types.to_string)
  in
  desc >:: fun _ ->
  assert_equal ~msg ~cmp:(value_eq eq) ~printer expected type_is_verified

let mz_is_mz = check "mz_is_mz" Float64.minus_zero Types.MinusZero Bool.tr

let mz_is_not_signed31 =
  check "mz_is_not_signed31" Float64.minus_zero Types.Signed31 Bool.fl

let mz_is_not_in_plain_number_or_nan =
  check "mz_is_not_in_plain_number_or_nan" Float64.minus_zero
    (Types.Union [ Types.PlainNumber; Types.NaN ])
    Bool.fl

let nan_is_nan = check "nan_is_nan" Float64.nan Types.NaN Bool.tr

let nan_is_number = check "nan_is_number" Float64.nan Types.Number Bool.tr

let nan_is_not_unsigned32 =
  check "nan_is_not_unsigned32" Float64.nan Types.Unsigned32 Bool.fl

let f64_minus_1073741824_is_number =
  check "f64_minus_1073741824_is_number"
    (Float64.of_float (-1073741824.000002861022))
    Types.Number Bool.tr

let mz_is_u32_or_mz =
  check "mz_is_u32_or_mz" Float64.minus_zero
    (Types.Union [ Types.Unsigned32; Types.MinusZero ])
    Bool.tr

let mz_is_not_u32_or_nan =
  check "mz_is_not_u32_or_nan" Float64.minus_zero
    (Types.Union [ Types.Unsigned32; Types.NaN ])
    Bool.fl

let simple_in_range =
  check "3.5_in_-100_to_100" (Float64.of_float 3.5)
    (Types.Range (-100., 100.))
    Bool.tr

let simple_not_in_range =
  check "3.5_not_in_-1_to_1" (Float64.of_float 3.5)
    (Types.Range (-1., 1.))
    Bool.fl

let i64_minus_one_not_in_0_and_4294967295 =
  check "i64:-1_not_in_0_and_4294967295"
    (Value.from_int (-1) |> Value.cast Type.int64)
    (Types.Range (0., 4294967295.))
    Bool.fl

let i32_zero_in_4294967295_and_4294967296 =
  check "i32:0_in_4294967295_and_4294967296"
    (Value.from_int 0 |> Value.cast Type.int32)
    (Types.Range (4294967295., 4294967296.))
    Bool.tr

let i32_2147483647_in_2147483647_and_2147483649 =
  check "i32:2147483647_in_2147483647_and_2147483649"
    (Value.from_int 2147483647 |> Value.cast Type.int32)
    (Types.Range (2147483647., 2147483649.))
    Bool.tr

let i32_m2147483648_in_2147483647_and_2147483649 =
  check "i32:m2147483648_in_2147483647_and_2147483649"
    (Value.from_int (-2147483648) |> Value.cast Type.int32)
    (Types.Range (2147483647., 2147483649.))
    Bool.tr

let ts_m67117101_in_m2147483648_and_2147483647 =
  check "ts_m67117101_in_m2147483648_and_2147483647"
    (mk_tagged_signed (-67117101))
    (Types.Range (-2147483648., 2147483647.))
    Bool.tr

let i64_m3238265527_in_m4294967295_and_0 =
  check "i64_m3238265527_in_m4294967295_and_0" (mk_int64 (-3238265527))
    (Types.Range (-4294967295., 0.))
    Bool.tr

let suite =
  "typer test suite"
  >::: [
         mz_is_mz;
         mz_is_not_signed31;
         mz_is_not_in_plain_number_or_nan;
         nan_is_nan;
         nan_is_number;
         nan_is_not_unsigned32;
         f64_minus_1073741824_is_number;
         mz_is_u32_or_mz;
         mz_is_not_u32_or_nan;
         simple_in_range;
         simple_not_in_range;
         i64_minus_one_not_in_0_and_4294967295;
         i32_zero_in_4294967295_and_4294967296;
         i32_2147483647_in_2147483647_and_2147483649;
         i32_m2147483648_in_2147483647_and_2147483649;
         ts_m67117101_in_m2147483648_and_2147483647;
         i64_m3238265527_in_m4294967295_and_0;
       ]

let _ = OUnit2.run_test_tt_main suite