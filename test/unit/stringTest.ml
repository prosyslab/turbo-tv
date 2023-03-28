open Helper

let from_string_tests =
  let name = "String::from_string" in
  let msg = "\027[91m" ^ name ^ "\027[0m" in
  let from_string_eq_test s expected =
    let actual = Strings.from_string s in
    let eq = Strings.equal_test in
    let _ = value_eq eq actual expected in
    name >:: fun _ ->
    assert_equal ~msg ~cmp:(value_eq eq) ~printer:(string_printer ~indent:1)
      expected actual
  in
  [
    from_string_eq_test "String[4]: #helloworld"
      (Strings.from_string "String[4]: #helloworld");
    from_string_eq_test "String[4]: #" (Strings.from_string "String[4]: \"\"");
    from_string_eq_test "String[4]: #aa"
      (Strings.from_string "String[4]: \"aa\"");
  ]

let concat_tests =
  let name = "String::concat" in
  let msg = "\027[91m" ^ name ^ "\027[0m" in
  let concat_eq_test s expected =
    let actual = s in
    let eq = Strings.equal_test in
    let _ = value_eq eq actual expected in
    name >:: fun _ ->
    assert_equal ~msg ~cmp:(value_eq eq) ~printer:(string_printer ~indent:1)
      expected actual
  in
  [
    concat_eq_test
      (Strings.concat
         (Strings.from_string "String[4]: #hello")
         (Strings.from_string "String[4]: #world"))
      (Strings.from_string "String[4]: #helloworld");
    concat_eq_test
      (Strings.concat
         (Strings.from_string "String[4]: #")
         (Strings.from_string "String[4]: #"))
      (Strings.from_string "String[4]: \"\"");
  ]

let length_tests =
  let name = "String::length" in
  let msg = "\027[91m" ^ name ^ "\027[0m" in
  let length_eq_test s expected =
    let actual = s in
    let eq = Value.eq in
    let _ = value_eq eq actual expected in
    name >:: fun _ ->
    assert_equal ~msg ~cmp:(value_eq eq) ~printer:(value_printer ~indent:1)
      expected actual
  in
  [
    length_eq_test
      (Strings.length (Strings.from_string "String[4]: #helloworld"))
      (Value.from_int 10 |> Value.cast Type.uint32);
    length_eq_test
      (Strings.length (Strings.from_string "String[4]: #"))
      (Value.from_int 0 |> Value.cast Type.uint32);
    length_eq_test
      (Strings.length
         (Strings.concat
            (Strings.from_string "String[4]: #hello")
            (Strings.from_string "String[4]: #world")))
      (Value.from_int 10 |> Value.cast Type.uint32);
  ]

let from_char_bv_test =
  let name = "String::from_char_bv" in
  let msg = "\027[91m" ^ name ^ "\027[0m" in
  let from_char_bv_eq_test s expected =
    let actual = s in
    let eq = Strings.equal_test in
    let _ = value_eq eq actual expected in
    name >:: fun _ ->
    assert_equal ~msg ~cmp:(value_eq eq) ~printer:(string_printer ~indent:1)
      expected actual
  in
  [
    from_char_bv_eq_test
      (Strings.from_char_bv (BitVecVal.from_string "c"))
      (Strings.from_string "String[4]: #c");
    from_char_bv_eq_test
      (Strings.from_char_bv (BitVecVal.from_string "a"))
      (Strings.from_string "String[4]: \"a\"");
  ]

let nth_test =
  let name = "String::nth_test" in
  let msg = "\027[91m" ^ name ^ "\027[0m" in
  let nth_eq_test s expected =
    let actual = s in
    let eq = Bool.eq in
    let _ = value_eq eq actual expected in
    name >:: fun _ ->
    assert_equal ~msg ~cmp:(value_eq eq)
      ~printer:(z3_expr_printer ~indent:1)
      expected actual
  in
  [
    nth_eq_test
      (Strings.nth
         (Strings.from_string "String[4]: #helloworld")
         (Value.from_int 1 |> Value.cast Type.uint32))
      (Str.nthi (Strings.from_string "String[4]: #e").value 0);
    nth_eq_test
      (Strings.nth
         (Strings.from_string "String[4]: #helloworld")
         (Value.from_int 0 |> Value.cast Type.uint32))
      (Str.nthi (Strings.from_string "String[4]: #h").value 0);
  ]

let index_of_test =
  let name = "String::index_of_test" in
  let msg = "\027[91m" ^ name ^ "\027[0m" in
  let index_of_eq_test s expected =
    let actual = s in
    let eq = Value.eq in
    let _ = value_eq eq actual expected in
    name >:: fun _ ->
    assert_equal ~msg ~cmp:(value_eq eq) ~printer:(value_printer ~indent:1)
      expected actual
  in
  [
    index_of_eq_test
      (Strings.index_of
         (Strings.from_string "String[4]: #helloworld")
         (Strings.from_string "String[4]: #llo")
         (Value.from_int 0))
      (Value.from_int 2 |> Value.cast Type.uint32);
  ]

let le_test =
  let name = "String::le" in
  let msg = "\027[91m" ^ name ^ "\027[0m" in
  let le_eq_test s expected =
    let actual = s in
    let eq = Value.eq in
    let _ = value_eq eq actual expected in
    name >:: fun _ ->
    assert_equal ~msg ~cmp:(value_eq eq)
      ~printer:(z3_expr_printer ~indent:1)
      expected actual
  in
  [
    le_eq_test
      (Strings.le
         (Strings.from_string "String[4]: #abcd")
         (Strings.from_string "String[4]: #abcd"))
      Value.tr;
    le_eq_test
      (Strings.le
         (Strings.from_string "String[4]: #abc")
         (Strings.from_string "String[4]: #abcd"))
      Value.tr;
    le_eq_test
      (Strings.le
         (Strings.from_string "String[4]: #abcd")
         (Strings.from_string "String[4]: #abcef"))
      Value.tr;
  ]

let lt_test =
  let name = "String::lt" in
  let msg = "\027[91m" ^ name ^ "\027[0m" in
  let lt_eq_test s expected =
    let actual = s in
    let eq = Value.eq in
    let _ = value_eq eq actual expected in
    name >:: fun _ ->
    assert_equal ~msg ~cmp:(value_eq eq)
      ~printer:(z3_expr_printer ~indent:1)
      expected actual
  in
  [
    lt_eq_test
      (Strings.lt
         (Strings.from_string "String[4]: #abcd")
         (Strings.from_string "String[4]: #abcd"))
      Value.fl;
    lt_eq_test
      (Strings.lt
         (Strings.from_string "String[4]: #abc")
         (Strings.from_string "String[4]: #abcd"))
      Value.tr;
    lt_eq_test
      (Strings.lt
         (Strings.from_string "String[4]: #abcd")
         (Strings.from_string "String[4]: #abcef"))
      Value.tr;
  ]

let sub_string_test =
  let name = "String::sub_string" in
  let msg = "\027[91m" ^ name ^ "\027[0m" in
  let sub_string_eq_test s expected =
    let actual = s in
    let eq = Strings.equal_test in
    let _ = value_eq eq actual expected in
    name >:: fun _ ->
    assert_equal ~msg ~cmp:(value_eq eq) ~printer:(string_printer ~indent:1)
      expected actual
  in
  [
    sub_string_eq_test
      (Strings.sub_string
         (Strings.from_string "String[4]: #abcdefg")
         (Value.from_int 0 |> Value.cast Type.uint32)
         (Value.from_int 3 |> Value.cast Type.uint32))
      (Strings.from_string "String[4]: #abc");
    sub_string_eq_test
      (Strings.sub_string
         (Strings.from_string "String[4]: #abcdefg")
         (Value.from_int 1 |> Value.cast Type.uint32)
         (Strings.length (Strings.from_string "String[4]: #abc")))
      (Strings.from_string "String[4]: #bcd");
    sub_string_eq_test
      (Strings.sub_string
         (Strings.from_string "String[4]: #abcdefg")
         (Value.from_int 0 |> Value.cast Type.uint32)
         (Strings.length (Strings.from_string "String[4]: #abcdefg")))
      (Strings.from_string "String[4]: #abcdefg");
  ]

let num2str_test =
  let name = "String::num2str" in
  let msg = "\027[91m" ^ name ^ "\027[0m" in
  let num2str_eq_test s expected =
    let actual = s in
    let eq = Strings.equal_test in
    let _ = value_eq eq actual expected in
    name >:: fun _ ->
    assert_equal ~msg ~cmp:(value_eq eq) ~printer:(string_printer ~indent:1)
      expected actual
  in
  [
    num2str_eq_test
      (Strings.num2str (Value.from_int 0 |> Value.cast Type.uint32))
      (Strings.from_string "String[4]: #0");
    num2str_eq_test
      (Strings.num2str (Value.from_int 100 |> Value.cast Type.uint32))
      (Strings.from_string "String[4]: #100");
  ]

let suite =
  "suite"
  >::: from_string_tests @ concat_tests @ length_tests @ from_char_bv_test
       @ nth_test @ index_of_test @ lt_test @ le_test @ sub_string_test
       @ num2str_test

let _ = OUnit2.run_test_tt_main suite