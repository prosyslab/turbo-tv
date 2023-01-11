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

let i32_to_i32_value i = i |> Value.from_int |> Value.cast Type.int32

let i32_to_tagged_signed i =
  BitVec.shli (i |> Value.from_int) 1 |> Value.cast Type.tagged_signed

let f_to_f64_value f = f |> Value.from_f64string |> Value.cast Type.float64

let f_to_heap_number ns = ns |> HeapNumber.from_number_string

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

let value_printer ?(indent = 0) e =
  let model = Z3utils.Solver.get_model solver |> Option.get in
  let indent = repeat "  " indent in
  String.concat "\n"
    [
      Format.sprintf "\n%sFormatted: %s" indent
        (e |> Printer.value_to_string model state.register_file state.memory);
      Format.sprintf "%sRaw: %s" indent (e |> Expr.to_simplified_string);
    ]

let apply_sem_v1m sem n =
  state |> sem n state.memory |> State.register_file |> RegisterFile.find "0"
