open Err
open Z3utils

type t = Bool.t

let init name = Bool.init name

let empty = Bool.fl

let to_string model uid = uid |> Model.eval model |> Expr.to_simplified_string

module UBFile = struct
  module U = Map.Make (String)

  let prefix = ref ""

  let uid id = !prefix ^ id

  let init stage =
    prefix := String.sub stage 0 1 ^ "u";
    U.empty

  let add key value uf = U.add key value uf

  let find uid uf =
    let uid = !prefix ^ uid in
    try U.find uid uf
    with Not_found ->
      let cause = uid in
      let reason = Format.sprintf "Cannot find %s from UBFile" cause in
      err (IdNotFound (cause, reason))

  let find_all uids cf = List.map (fun uid -> find uid cf) uids

  let empty = U.empty

  let iter = U.iter
end
