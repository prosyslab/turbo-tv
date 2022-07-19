open Z3utils
module UBFile = ExprMap.Make (Bool)

type t = Bool.t

let init name = Bool.init name

let empty = Bool.fl

let to_string model uid = uid |> Model.eval model |> Expr.to_simplified_string

let symbol = "u"
