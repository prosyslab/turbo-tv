open Err
open Z3utils

module M = Map.Make (struct
  type t = int

  let compare = compare
end)

type bid = int

let bid = ref 0
let add = M.add

let allocate nbytes mem =
  let nbid = !bid in
  let block =
    BitVec.init ~len:(nbytes * 8) ("block" ^ (nbid |> string_of_int))
  in
  let updated = M.add nbid block mem in
  bid := nbid + 1;
  (nbid, updated)

let find bid mem =
  try M.find bid mem
  with Not_found ->
    let cause = bid |> string_of_int in
    let reason = Format.sprintf "Cannot find %s from RegisterFile" cause in
    err (IdNotFound (cause, reason))

let size bid mem =
  let block = find bid mem in
  BitVec.len block

let read bid pos size mem =
  let block = find bid mem in
  BitVec.extract (((pos + size) * 8) - 1) (pos * 8) block

let write bid pos size value mem =
  let target = read bid pos size mem in
  Bool.eq value target

let empty = M.empty
let iter = M.iter
