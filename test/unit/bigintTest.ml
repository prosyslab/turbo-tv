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

let suite =
  "suite"
  >::: from_string_tests @ neg_tests @ add_tests @ sub_tests @ mul_tests
       @ div_tests @ rem_tests @ shift_left_tests @ shift_right_tests

let _ = OUnit2.run_test_tt_main suite
