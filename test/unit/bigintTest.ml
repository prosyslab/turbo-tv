(* Unit test of Bigint module *)
open Helper

let from_string_tests =
  let name = "BigInt::from_string" in
  let msg = "\027[91m" ^ name ^ "\027[0m" in
  let from_string_eq_test s expected =
    let actual = Bigint.from_string s in
    let eq = Bigint.equal in
    let _ = value_eq eq actual expected in
    name >:: fun _ ->
    assert_equal ~msg ~cmp:(value_eq eq) ~printer:(bigint_printer ~indent:1)
      expected actual
  in
  [
    from_string_eq_test "BigInt + 0" Bigint.zero;
    from_string_eq_test "BigInt - 1" (Bigint.from_int (-1));
    from_string_eq_test "BigInt + 4611686018427387903"
      (Bigint.from_int Int.max_int);
    from_string_eq_test "BigInt - 4611686018427387904"
      (Bigint.from_int Int.min_int);
  ]

let neg_tests =
  let name = "BigInt::neg" in
  let msg = "\027[91m" ^ name ^ "\027[0m" in
  let neg_eq_test v expected =
    let actual = Bigint.neg v in
    let eq = Bigint.equal in
    let _ = value_eq eq actual expected in
    name >:: fun _ ->
    assert_equal ~msg ~cmp:(value_eq eq) ~printer:(bigint_printer ~indent:1)
      expected actual
  in
  [
    neg_eq_test Bigint.zero Bigint.zero;
    neg_eq_test (Bigint.from_int (-1)) (Bigint.from_int 1);
    neg_eq_test (Bigint.from_int 1) (Bigint.from_int (-1));
  ]

let add_tests =
  let name = "BigInt::add" in
  let msg = "\027[91m" ^ name ^ "\027[0m" in
  let add_eq_test l r expected =
    let actual = Bigint.add l r in
    let eq = Bigint.equal in
    let _ = value_eq eq actual expected in
    name >:: fun _ ->
    assert_equal ~msg ~cmp:(value_eq eq) ~printer:(bigint_printer ~indent:1)
      expected actual
  in
  [
    add_eq_test Bigint.zero Bigint.zero Bigint.zero;
    add_eq_test (Bigint.from_int 1) (Bigint.from_int 1) (Bigint.from_int 2);
    add_eq_test (Bigint.from_int (-1)) (Bigint.from_int (-1))
      (Bigint.from_int (-2));
    add_eq_test (Bigint.from_int 1) (Bigint.from_int (-1)) Bigint.zero;
    add_eq_test
      (Bigint.from_int 0xdeadbeef)
      (Bigint.from_int 0xcafebabe)
      (Bigint.from_int 0x1a9ac79ad);
  ]

let sub_tests =
  let name = "BigInt::sub" in
  let msg = "\027[91m" ^ name ^ "\027[0m" in
  let sub_eq_test l r expected =
    let actual = Bigint.sub l r in
    let eq = Bigint.equal in
    let _ = value_eq eq actual expected in
    name >:: fun _ ->
    assert_equal ~msg ~cmp:(value_eq eq) ~printer:(bigint_printer ~indent:1)
      expected actual
  in
  [
    sub_eq_test Bigint.zero Bigint.zero Bigint.zero;
    sub_eq_test (Bigint.from_int (-1)) (Bigint.from_int (-1)) Bigint.zero;
    sub_eq_test (Bigint.from_int 0) (Bigint.from_int (-1)) (Bigint.from_int 1);
    sub_eq_test
      (Bigint.from_int 0xdeadbeef)
      (Bigint.from_int 0xcafebabe)
      (Bigint.from_int 0x13af0431);
    sub_eq_test
      (Bigint.from_int 0xcafebabe)
      (Bigint.from_int 0xdeadbeef)
      (Bigint.from_int (-0x13af0431));
  ]

let mul_tests =
  let name = "BigInt::mul" in
  let msg = "\027[91m" ^ name ^ "\027[0m" in
  let mul_eq_test l r expected =
    let actual = Bigint.mul l r in
    let eq = Bigint.equal in
    let _ = value_eq eq actual expected in
    name >:: fun _ ->
    assert_equal ~msg ~cmp:(value_eq eq) ~printer:(bigint_printer ~indent:1)
      expected actual
  in
  [
    mul_eq_test Bigint.zero Bigint.zero Bigint.zero;
    mul_eq_test Bigint.zero (Bigint.from_int 1) Bigint.zero;
    mul_eq_test (Bigint.from_int 1) (Bigint.from_int (-1))
      (Bigint.from_int (-1));
    mul_eq_test (Bigint.from_int (-1)) (Bigint.from_int (-1))
      (Bigint.from_int 1);
    mul_eq_test
      (Bigint.from_int 0x41414141)
      (Bigint.from_int 0x41414141)
      (Bigint.from_int 0x10a233c535a41281);
  ]

let div_tests =
  let name = "BigInt::div" in
  let msg = "\027[91m" ^ name ^ "\027[0m" in
  let div_eq_test l r expected =
    let actual = Bigint.div l r in
    let eq = Bigint.equal in
    let _ = value_eq eq actual expected in
    name >:: fun _ ->
    assert_equal ~msg ~cmp:(value_eq eq) ~printer:(bigint_printer ~indent:1)
      expected actual
  in
  [
    div_eq_test (Bigint.from_int 1) (Bigint.from_int 1) (Bigint.from_int 1);
    div_eq_test (Bigint.from_int 1) (Bigint.from_int (-1))
      (Bigint.from_int (-1));
    div_eq_test (Bigint.from_int (-1)) (Bigint.from_int (-1))
      (Bigint.from_int 1);
    div_eq_test
      (Bigint.from_int 0xdeadbeef)
      (Bigint.from_int 0xcafebabe)
      (Bigint.from_int 1);
    div_eq_test
      (Bigint.from_int 0x41414141)
      (Bigint.from_int 0x41414142)
      Bigint.zero;
    div_eq_test
      (Bigint.from_int (-0x123456789abcdef))
      (Bigint.from_int 0x41414141)
      (Bigint.from_int (-74886609));
    div_eq_test
      (Bigint.from_int 0x123456789abcdef)
      (Bigint.from_int 0x41414141)
      (Bigint.from_int 74886609);
  ]

let rem_tests =
  let name = "BigInt::rem" in
  let msg = "\027[91m" ^ name ^ "\027[0m" in
  let rem_eq_test l r expected =
    let actual = Bigint.rem l r in
    let eq = Bigint.equal in
    let _ = value_eq eq actual expected in
    name >:: fun _ ->
    assert_equal ~msg ~cmp:(value_eq eq) ~printer:(bigint_printer ~indent:1)
      expected actual
  in
  [
    rem_eq_test (Bigint.from_int 1) (Bigint.from_int 1) Bigint.zero;
    rem_eq_test (Bigint.from_int 1) (Bigint.from_int (-1)) Bigint.zero;
    rem_eq_test (Bigint.from_int (-1)) (Bigint.from_int (-1)) Bigint.zero;
    rem_eq_test
      (Bigint.from_int 0xdeadbeef)
      (Bigint.from_int 0xcafebabe)
      (Bigint.from_int 0x13af0431);
    rem_eq_test
      (Bigint.from_int 0x41414141)
      (Bigint.from_int 0x41414142)
      (Bigint.from_int 0x41414141);
    rem_eq_test
      (Bigint.from_int (-0x123456789abcdef))
      (Bigint.from_int 0x41414141)
      (Bigint.from_int (-307665630));
    rem_eq_test
      (Bigint.from_int 0x123456789abcdef)
      (Bigint.from_int 0x41414141)
      (Bigint.from_int 307665630);
  ]

let bitwise_and_tests =
  let name = "BigInt::bitwise_and" in
  let msg = "\027[91m" ^ name ^ "\027[0m" in
  let bitwise_and_eq_test l r expected =
    let actual = Bigint.bitwise_and l r in
    let eq = Bigint.equal in
    let _ = value_eq eq actual expected in
    name >:: fun _ ->
    assert_equal ~msg ~cmp:(value_eq eq) ~printer:(bigint_printer ~indent:1)
      expected actual
  in
  [
    bitwise_and_eq_test Bigint.zero Bigint.zero Bigint.zero;
    bitwise_and_eq_test Bigint.zero (Bigint.from_int 1) Bigint.zero;
    bitwise_and_eq_test (Bigint.from_int 1) (Bigint.from_int (-1))
      (Bigint.from_int 1);
    bitwise_and_eq_test (Bigint.from_int (-1)) (Bigint.from_int (-2))
      (Bigint.from_int (-2));
    bitwise_and_eq_test
      (Bigint.from_int 0xdeadbeef)
      (Bigint.from_int 0xcafebabe)
      (Bigint.from_int 0xcaacbaae);
    bitwise_and_eq_test
      (Bigint.from_int (-0x123456789abcdef))
      (Bigint.from_int 0x41414141)
      (Bigint.from_int 0x40400001);
  ]

let bitwise_or_tests =
  let name = "BigInt::bitwise_or" in
  let msg = "\027[91m" ^ name ^ "\027[0m" in
  let bitwise_or_eq_test l r expected =
    let actual = Bigint.bitwise_or l r in
    let eq = Bigint.equal in
    let _ = value_eq eq actual expected in
    name >:: fun _ ->
    assert_equal ~msg ~cmp:(value_eq eq) ~printer:(bigint_printer ~indent:1)
      expected actual
  in
  [
    bitwise_or_eq_test Bigint.zero Bigint.zero Bigint.zero;
    bitwise_or_eq_test Bigint.zero (Bigint.from_int 1) (Bigint.from_int 1);
    bitwise_or_eq_test (Bigint.from_int 1) (Bigint.from_int (-1))
      (Bigint.from_int (-1));
    bitwise_or_eq_test (Bigint.from_int (-1)) (Bigint.from_int (-1))
      (Bigint.from_int (-1));
    bitwise_or_eq_test
      (Bigint.from_int 0xdeadbeef)
      (Bigint.from_int 0xcafebabe)
      (Bigint.from_int 0xdeffbeff);
    bitwise_or_eq_test
      (Bigint.from_int (-0x41414141))
      (Bigint.from_int 0x41414142)
      (Bigint.from_int (-1));
  ]

let bitwise_xor_tests =
  let name = "BigInt::bitwise_xor" in
  let msg = "\027[91m" ^ name ^ "\027[0m" in
  let bitwise_xor_eq_test l r expected =
    let actual = Bigint.bitwise_xor l r in
    let eq = Bigint.equal in
    let _ = value_eq eq actual expected in
    name >:: fun _ ->
    assert_equal ~msg ~cmp:(value_eq eq) ~printer:(bigint_printer ~indent:1)
      expected actual
  in
  [
    bitwise_xor_eq_test Bigint.zero Bigint.zero Bigint.zero;
    bitwise_xor_eq_test Bigint.zero (Bigint.from_int 1) (Bigint.from_int 1);
    bitwise_xor_eq_test (Bigint.from_int 1) (Bigint.from_int (-1))
      (Bigint.from_int (-2));
    bitwise_xor_eq_test (Bigint.from_int (-1)) (Bigint.from_int (-1))
      Bigint.zero;
    bitwise_xor_eq_test (Bigint.from_int (-1)) (Bigint.from_int 0)
      (Bigint.from_int (-1));
  ]

let shift_left_tests =
  let name = "BigInt::shift_left" in
  let msg = "\027[91m" ^ name ^ "\027[0m" in
  let shift_left_eq_test v n expected =
    let actual = Bigint.shift_left v (Bigint.from_int n) in
    let eq = Bigint.equal in
    let _ = value_eq eq actual expected in
    name >:: fun _ ->
    assert_equal ~msg ~cmp:(value_eq eq) ~printer:(bigint_printer ~indent:1)
      expected actual
  in
  [
    shift_left_eq_test Bigint.zero 0 Bigint.zero;
    shift_left_eq_test Bigint.zero 1 Bigint.zero;
    shift_left_eq_test (Bigint.from_int 1) 0 (Bigint.from_int 1);
    shift_left_eq_test (Bigint.from_int 1) 1 (Bigint.from_int 2);
    shift_left_eq_test (Bigint.from_int 1) 2 (Bigint.from_int 4);
    shift_left_eq_test (Bigint.from_int 1) 3 (Bigint.from_int 8);
    shift_left_eq_test (Bigint.from_int 1) 4 (Bigint.from_int 16);
    shift_left_eq_test (Bigint.from_int 1) 5 (Bigint.from_int 32);
    shift_left_eq_test (Bigint.from_int 1) 6 (Bigint.from_int 64);
    shift_left_eq_test (Bigint.from_int 1) 7 (Bigint.from_int 128);
    shift_left_eq_test (Bigint.from_int 1) 8 (Bigint.from_int 256);
    shift_left_eq_test (Bigint.from_int 1) 9 (Bigint.from_int 512);
    shift_left_eq_test (Bigint.from_int 1) 10 (Bigint.from_int 1024);
    shift_left_eq_test (Bigint.from_int 1) 11 (Bigint.from_int 2048);
    shift_left_eq_test (Bigint.from_int 1) 12 (Bigint.from_int 4096);
    shift_left_eq_test (Bigint.from_int 1) 13 (Bigint.from_int 8192);
    shift_left_eq_test (Bigint.from_int 1) 14 (Bigint.from_int 16384);
  ]

let shift_right_tests =
  let name = "BigInt::shift_right" in
  let msg = "\027[91m" ^ name ^ "\027[0m" in
  let shift_right_eq_test v n expected =
    let actual = Bigint.shift_right v (Bigint.from_int n) in
    let eq = Bigint.equal in
    let _ = value_eq eq actual expected in
    name >:: fun _ ->
    assert_equal ~msg ~cmp:(value_eq eq) ~printer:(bigint_printer ~indent:1)
      expected actual
  in
  [
    shift_right_eq_test Bigint.zero 0 Bigint.zero;
    shift_right_eq_test Bigint.zero 1 Bigint.zero;
    shift_right_eq_test (Bigint.from_int 1) 0 (Bigint.from_int 1);
    shift_right_eq_test (Bigint.from_int 2) 1 (Bigint.from_int 1);
    shift_right_eq_test (Bigint.from_int 4) 2 (Bigint.from_int 1);
    shift_right_eq_test (Bigint.from_int 8) 3 (Bigint.from_int 1);
    shift_right_eq_test (Bigint.from_int 16) 4 (Bigint.from_int 1);
    shift_right_eq_test (Bigint.from_int 32) 5 (Bigint.from_int 1);
    shift_right_eq_test (Bigint.from_int 64) 6 (Bigint.from_int 1);
    shift_right_eq_test (Bigint.from_int 128) 7 (Bigint.from_int 1);
    shift_right_eq_test (Bigint.from_int 256) 8 (Bigint.from_int 1);
    shift_right_eq_test (Bigint.from_int 512) 9 (Bigint.from_int 1);
    shift_right_eq_test (Bigint.from_int 1024) 10 (Bigint.from_int 1);
    shift_right_eq_test (Bigint.from_int 2048) 11 (Bigint.from_int 1);
    shift_right_eq_test (Bigint.from_int 4096) 12 (Bigint.from_int 1);
    shift_right_eq_test (Bigint.from_int 8192) 13 (Bigint.from_int 1);
    shift_right_eq_test (Bigint.from_int 16384) 14 (Bigint.from_int 1);
  ]

let equal_tests =
  let name = "BigInt::equal" in
  let msg = "\027[91m" ^ name ^ "\027[0m" in
  let equal_test v1 v2 expected =
    let actual = Bigint.equal v1 v2 in
    let expected = if expected then Bool.tr else Bool.fl in
    let eq = Bool.eq in
    let _ = value_eq eq actual expected in
    name >:: fun _ ->
    assert_equal ~msg ~cmp:(value_eq eq)
      ~printer:(z3_expr_printer ~indent:1)
      expected actual
  in
  [
    equal_test Bigint.zero Bigint.zero true;
    equal_test Bigint.zero (Bigint.from_int 1) false;
    equal_test (Bigint.from_int 1) (Bigint.from_int 1) true;
    equal_test (Bigint.from_int 1) (Bigint.from_int 2) false;
    equal_test (Bigint.from_int 1) (Bigint.from_int (-1)) false;
    equal_test (Bigint.from_int (-1)) (Bigint.from_int (-1)) true;
    equal_test (Bigint.from_int (-1)) (Bigint.from_int 0) false;
    equal_test Bigint.zero
      (Bigint.from_string "BigInt + 4611686018427387903 4611686018427387903")
      false;
    equal_test
      (Bigint.from_string "BigInt + 4611686018427387903 4611686018427387903")
      (Bigint.from_string "BigInt + 4611686018427387903 4611686018427387903")
      true;
    equal_test
      (Bigint.from_string "BigInt - 4611686018427387903 4611686018427387903")
      (Bigint.from_string "BigInt + 4611686018427387903 4611686018427387903")
      false;
  ]

let less_than_tests =
  let name = "BigInt::less_than" in
  let less_than_test v1 v2 expected =
    let msg = Format.sprintf "\027[91m%s\027[0m" name in
    let actual = Bigint.less_than v1 v2 in
    let expected = if expected then Bool.tr else Bool.fl in
    let eq = Bool.eq in
    let _ = value_eq eq actual expected in
    name >:: fun _ ->
    assert_equal ~msg ~cmp:(value_eq eq)
      ~printer:(z3_expr_printer ~indent:1)
      expected actual
  in
  [
    less_than_test Bigint.zero Bigint.zero false;
    less_than_test Bigint.zero (Bigint.from_int 1) true;
    less_than_test (Bigint.from_int 1) (Bigint.from_int 1) false;
    less_than_test (Bigint.from_int 1) (Bigint.from_int 2) true;
    less_than_test (Bigint.from_int 1) (Bigint.from_int (-1)) false;
    less_than_test (Bigint.from_int (-1)) (Bigint.from_int (-1)) false;
    less_than_test (Bigint.from_int (-1)) (Bigint.from_int 0) true;
    less_than_test Bigint.zero
      (Bigint.from_string "BigInt + 4611686018427387903 4611686018427387903")
      true;
    less_than_test
      (Bigint.from_string "BigInt + 4611686018427387903 4611686018427387903")
      (Bigint.from_string "BigInt + 4611686018427387903 4611686018427387903")
      false;
    less_than_test
      (Bigint.from_string "BigInt - 4611686018427387903 4611686018427387903")
      (Bigint.from_string "BigInt + 4611686018427387904 4611686018427387903")
      true;
  ]

let as_intN_tests =
  let name = "BigInt::as_intN" in
  let as_intN_test n v expected =
    let msg = Format.sprintf "\027[91m%s\027[0m" name in
    let actual = Bigint.as_intN n v in
    let eq = Bigint.equal in
    let _ = value_eq eq actual expected in
    name >:: fun _ ->
    assert_equal ~msg ~cmp:(value_eq eq) ~printer:(bigint_printer ~indent:1)
      expected actual
  in
  [
    as_intN_test 0 (Bigint.from_int 1) Bigint.zero;
    as_intN_test 1 Bigint.zero Bigint.zero;
    as_intN_test 1 (Bigint.from_int 1) (Bigint.from_int (-1));
    as_intN_test 1 (Bigint.from_int (-1)) (Bigint.from_int (-1));
    as_intN_test 32 (Bigint.from_int 2147483647) (Bigint.from_int 2147483647);
    as_intN_test 32 (Bigint.from_int 2147483648) (Bigint.from_int (-2147483648));
    as_intN_test 32
      (Bigint.from_int (-2147483648))
      (Bigint.from_int (-2147483648));
    as_intN_test 32 (Bigint.from_int 0xcafebabe) (Bigint.from_int (-889275714));
    as_intN_test 32 (Bigint.from_int 0xdeadbeef) (Bigint.from_int (-559038737));
    as_intN_test 64 (Bigint.from_int 0xdeadbeef) (Bigint.from_int 0xdeadbeef);
  ]

let as_uintN_tests =
  let name = "BigInt::as_uintN" in
  let as_uintN_test n v expected =
    let msg = Format.sprintf "\027[91m%s\027[0m" name in
    let actual = Bigint.as_uintN n v in
    let eq = Bigint.equal in
    let _ = value_eq eq actual expected in
    name >:: fun _ ->
    assert_equal ~msg ~cmp:(value_eq eq) ~printer:(bigint_printer ~indent:1)
      expected actual
  in
  [
    as_uintN_test 0 (Bigint.from_int 1) Bigint.zero;
    as_uintN_test 1 Bigint.zero Bigint.zero;
    as_uintN_test 1 (Bigint.from_int 1) (Bigint.from_int 1);
    as_uintN_test 1 (Bigint.from_int (-1)) (Bigint.from_int 1);
    as_uintN_test 32 (Bigint.from_int 2147483647) (Bigint.from_int 2147483647);
    as_uintN_test 32 (Bigint.from_int 2147483648) (Bigint.from_int 2147483648);
    as_uintN_test 32
      (Bigint.from_int (-2147483648))
      (Bigint.from_int 2147483648);
    as_uintN_test 32 (Bigint.from_int 0xcafebabe) (Bigint.from_int 0xcafebabe);
    as_uintN_test 32 (Bigint.from_int 0xdeadbeef) (Bigint.from_int 0xdeadbeef);
    as_uintN_test 64 (Bigint.from_int 0xdeadbeef) (Bigint.from_int 0xdeadbeef);
  ]

let suite =
  "suite"
  >::: from_string_tests @ neg_tests @ add_tests @ sub_tests @ mul_tests
       @ div_tests @ rem_tests @ bitwise_and_tests @ bitwise_or_tests
       @ bitwise_xor_tests @ shift_left_tests @ shift_right_tests @ equal_tests
       @ less_than_tests @ as_intN_tests @ as_uintN_tests

let _ = OUnit2.run_test_tt_main suite
