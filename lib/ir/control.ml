open Err
open Z3utils

type t = E.expr

let init name = Bool.init name

let empty = Bool.fl

let to_string model cid = cid |> Model.eval model |> Expr.to_simplified_string

(* only for branch *)
module ControlTuple = struct
  type t = E.expr

  let sort =
    Z3.Tuple.mk_sort ctx
      (Z3.Symbol.mk_string ctx "ControlTuple")
      [
        Z3.Symbol.mk_string ctx "TrueCond"; Z3.Symbol.mk_string ctx "FalseCond";
      ]
      [ Bool.mk_sort; Bool.mk_sort ]

  let ctor = sort |> Z3.Tuple.get_mk_decl

  let field_decls = sort |> Z3.Tuple.get_field_decls

  let init cid = E.mk_const_s ctx cid sort

  let from_tf for_true for_false =
    Z3.FuncDecl.apply ctor [ for_true; for_false ]

  let true_cond t =
    let true_decl = field_decls |> List.hd in
    Z3.FuncDecl.apply true_decl [ t ]

  let false_cond t =
    let false_decl = List.nth field_decls 1 in
    Z3.FuncDecl.apply false_decl [ t ]

  let eq lexp rexp =
    let true_cond_eq = Bool.eq (lexp |> true_cond) (rexp |> true_cond) in
    let false_cond_eq = Bool.eq (lexp |> false_cond) (rexp |> false_cond) in
    Bool.ands [ true_cond_eq; false_cond_eq ]
end

module ControlFile = struct
  module C = Map.Make (String)

  let prefix = ref ""

  let init stage =
    prefix :=
      if stage = "before" then "bc"
      else if stage = "after" then "ac"
      else failwith "Invalid stage";
    C.empty

  let add key value rf = C.add key value rf

  let find cid cf =
    let cid = !prefix ^ cid in
    try C.find cid cf
    with Not_found ->
      let cause = cid in
      let reason = Format.sprintf "Cannot find %s from ControlFile" cause in
      err (IdNotFound (cause, reason))

  let find_all cids cf = List.map (fun vid -> find vid cf) cids

  let empty = C.empty

  let iter = C.iter
end
