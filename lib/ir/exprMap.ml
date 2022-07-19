module type Expr = sig
  type t

  val empty : t
end

module Make (V : Expr) = struct
  module M = Map.Make (String)

  type t = { expr_map : V.t M.t; prefix : string }

  let prefix t = t.prefix

  let expr_map t = t.expr_map

  let get_id n t = prefix t ^ n

  let init stage symbol =
    { expr_map = M.empty; prefix = String.sub stage 0 1 ^ symbol }

  let add key value t =
    match value with
    | None -> t
    | Some v ->
        let expr_map = M.add (prefix t ^ key) v (expr_map t) in
        { expr_map; prefix = t.prefix }

  let find n t =
    let m = expr_map t in
    let id = get_id n t in
    try M.find id m with Not_found -> V.empty

  let find_all ids t = List.map (fun id -> find id t) ids

  let iter f t =
    let m = expr_map t in
    M.iter f m
end
