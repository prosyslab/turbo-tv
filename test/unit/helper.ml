include Lib
include Z3utils
include Simplified
include Machine
include Common
include ValueOperator
include OUnit2

let state = State.init 0 "test"

let solver = Z3utils.Solver.init None

let is_satisfiable expr =
  match Z3utils.Solver.check solver expr with
  | Z3.Solver.SATISFIABLE -> true
  | _ -> false

let is_unsatisfiable expr =
  match Solver.check solver expr with
  | Z3.Solver.UNSATISFIABLE -> true
  | _ -> false

let value_eq eq e1 e2 = eq e1 e2 |> is_satisfiable

let repeat s n =
  let rec helper s1 n1 = if n1 = 0 then s1 else helper (s1 ^ s) (n1 - 1) in
  helper "" n

let u32_to_u32_value u = u |> Value.from_int |> Value.cast Type.uint32

let z3_expr_printer ?(indent = 0) e =
  let indent = repeat "  " indent in
  Format.sprintf "\n%s%s\n" indent (e |> Expr.to_simplified_string)

let bigint_printer ?(indent = 0) bn =
  let model = Z3utils.Solver.get_model solver |> Option.get in
  let indent = repeat "  " indent in
  String.concat "\n"
    [
      Format.sprintf "\n%sFormatted: %s" indent (bn |> Bigint.to_string model);
      Format.sprintf "%sRaw: %s" indent (bn |> Bigint.to_bytestring model);
    ]

let string_printer ?(indent = 0) str =
  let model = Z3utils.Solver.get_model solver |> Option.get in
  let indent = repeat "  " indent in
  String.concat "\n"
    [
      Format.sprintf "\n%sFormatted: %s" indent (str |> Strings.to_string model);
      Format.sprintf "%sRaw: %s" indent (str.value |> Expr.to_simplified_string);
    ]

let value_printer ?(indent = 0) e =
  let model = Z3utils.Solver.get_model solver |> Option.get in
  let indent = repeat "  " indent in
  String.concat "\n"
    [
      Format.sprintf "\n%sFormatted: %s" indent
        (e |> Printer.value_to_string model state.register_file state.memory);
      Format.sprintf "%sRaw: %s" indent (e |> Expr.to_simplified_string);
    ]

let bool_printer ?(indent = 0) b =
  let model = Z3utils.Solver.get_model solver |> Option.get in
  let indent = repeat "  " indent in
  String.concat "\n"
    [
      Format.sprintf "\n%sFormatted: %s\n" indent
        (b |> Model.eval model |> Expr.to_simplified_string);
    ]

let false_cst = RegisterFile.find "false" state.register_file

let true_cst = RegisterFile.find "true" state.register_file

let null_cst = RegisterFile.find "null" state.register_file

let undefined_cst = RegisterFile.find "undefined" state.register_file

(* value constructors *)

let mk_tagged_signed i =
  BitVec.shli (i |> Value.from_int) 1 |> Value.cast Type.tagged_signed

let mk_float64 f = Float64.of_float f

let mk_int32 i = i |> Value.from_int |> Value.cast Type.int32

let mk_int64 i = i |> Value.from_int |> Value.cast Type.int64

let mk_uint32 i = i |> Value.from_int |> Value.cast Type.uint32

let mk_heap_number_ptr f =
  Heapnumber.from_float64 Bool.tr state.memory (mk_float64 f)

(* object constructors *)
let mk_heap_number f = Heapnumber.from_number_string (string_of_float f)

(* semantic applications *)
let apply_sem_v1m sem n =
  state |> sem n state.memory |> State.register_file |> RegisterFile.find "0"
