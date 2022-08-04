open Z3utils

(* JSGRAPH_SINGLETON_CONSTANT_LIST @ graph-assembler.h  *)
let names = [ "undefined"; "null"; "String[0]: #"; "false"; "true" ]

let is_constant name = List.mem name names

let is_undefined rf value = Value.eq (RegisterFile.find "undefined" rf) value

let is_null rf value = Value.eq (RegisterFile.find "null" rf) value

let is_empty_string rf value =
  Value.eq (RegisterFile.find "String[0]: #" rf) value

let is_false_cst rf value = Value.eq (RegisterFile.find "false" rf) value

let is_true_cst rf value = Value.eq (RegisterFile.find "true" rf) value

let is_constant_ptr model rf ptr =
  let evaluated = ptr |> Model.eval model in
  String.contains
    (evaluated |> is_undefined rf |> Expr.to_simplified_string)
    't'
  || String.contains (evaluated |> is_null rf |> Expr.to_simplified_string) 't'
  || String.contains
       (evaluated |> is_empty_string rf |> Expr.to_simplified_string)
       't'
  || String.contains
       (evaluated |> is_false_cst rf |> Expr.to_simplified_string)
       't'
  || String.contains
       (evaluated |> is_true_cst rf |> Expr.to_simplified_string)
       't'

let to_string model rf ptr =
  let evaluated = ptr |> Model.eval model in
  if
    String.contains
      (evaluated |> is_undefined rf |> Expr.to_simplified_string)
      't'
  then "HeapConstant(Undefined)"
  else if
    String.contains (evaluated |> is_null rf |> Expr.to_simplified_string) 't'
  then "HeapConstant(Null)"
  else if
    String.contains
      (evaluated |> is_empty_string rf |> Expr.to_simplified_string)
      't'
  then "HeapConstant(Empty String)"
  else if
    String.contains
      (evaluated |> is_false_cst rf |> Expr.to_simplified_string)
      't'
  then "HeapConstant(False)"
  else if
    String.contains
      (evaluated |> is_true_cst rf |> Expr.to_simplified_string)
      't'
  then "HeapConstant(True)"
  else evaluated |> Expr.to_simplified_string
