open Z3utils

type t = Bool.t

let init name = Bool.init name

let empty = Bool.fl

let to_string model uid = uid |> Model.eval model |> Expr.to_simplified_string

module UBFile = ExprMap.Make (Bool)

let symbol = "u"
