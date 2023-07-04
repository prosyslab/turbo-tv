#require "core_unix cmdliner ocamlgraph str re z3"

#load "_build/default/lib/lib.cma"

#directory "_build/default/lib/.lib.objs/byte"

open Lib.Z3utils
open Lib.ValueOperator

let pp exp = exp |> Expr.to_simplified_string |> print_endline

let pp_f exp = R.to_decimal_string (Expr.simplify None exp) 17 |> print_endline
