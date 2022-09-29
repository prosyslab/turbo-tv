open Helper

let printer = Expr.to_simplified_string

let check desc value ty expected =
  let type_is_verified = Typer.verify value ty state.memory in
  let eq = Bool.eq in
  let _ = value_eq eq type_is_verified expected in
  let msg =
    Format.sprintf "Value:\n%s\nType: %s\n"
      (value |> value_printer ~indent:1)
      (ty |> Types.to_string)
  in
  desc >:: fun _ ->
  assert_equal ~msg ~cmp:(value_eq eq) ~printer type_is_verified expected

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

let mz_is_u32_or_mz =
  check "mz_is_u32_or_mz" Float64.minus_zero
    (Types.Union [ Types.Unsigned32; Types.MinusZero ])
    Bool.tr

let mz_is_not_u32_or_nan =
  check "mz_is_not_u32_or_nan" Float64.minus_zero
    (Types.Union [ Types.Unsigned32; Types.NaN ])
    Bool.fl

let simple_in_range =
  check "3.5_in_-100_to_100" (Float64.from_numeral 3.5)
    (Types.Range (-100., 100.))
    Bool.tr

let simple_not_in_range =
  check "3.5_not_in_-1_to_1" (Float64.from_numeral 3.5)
    (Types.Range (-1., 1.))
    Bool.fl

let suite =
  "suite"
  >::: [
         mz_is_mz;
         mz_is_not_signed31;
         nan_is_nan;
         nan_is_number;
         nan_is_not_unsigned32;
         mz_is_u32_or_mz;
         mz_is_not_u32_or_nan;
         simple_in_range;
         simple_not_in_range;
       ]

let _ = OUnit2.run_test_tt_main suite