#require "z3"

#mod_use "lib/utils/err.ml"

#mod_use "lib/utils/z3utils.ml"

open Z3utils

let pp exp = exp |> Expr.to_simplified_string |> print_endline

let pp_f exp = R.to_decimal_string (Expr.simplify None exp) 17 |> print_endline
