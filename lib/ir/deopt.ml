open Z3utils

type t = Bool.t

let symbol = "d"

let init name = Bool.init name

let empty = Bool.fl

let to_string model did = did |> Model.eval model |> Expr.to_simplified_string
