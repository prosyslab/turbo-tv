open Err
module R = Map.Make (String)

let prefix = ref ""

let init stage =
  prefix := String.sub stage 0 1 ^ "v";
  R.empty

let add key value rf = R.add key value rf

let find vid rf =
  let vid = !prefix ^ vid in
  try R.find vid rf
  with Not_found ->
    let cause = vid in
    let reason = Format.sprintf "Cannot find %s from RegisterFile" cause in
    err (IdNotFound (cause, reason))

let find_all vids rf = List.map (fun vid -> find vid rf) vids

let empty = R.empty

let iter = R.iter
