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

let suite =
  "suite" >::: from_string_tests @ neg_tests @ add_tests @ sub_tests @ mul_tests

let _ = OUnit2.run_test_tt_main suite
