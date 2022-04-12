open Z3utils

type t = Array.t

let init name = Array.init name (BitVec.mk_sort Pointer.len) (BitVec.mk_sort 8)

let allocate vid size = Pointer.init vid size

(* Load [value] at block of [ptr] with the size [sz]*)
let load ptr sz mem =
  let rec aux res loaded_sz ptr =
    if loaded_sz = sz then res
    else
      let byte = Array.select ptr mem in
      let res = if loaded_sz = 0 then byte else BitVec.concat res byte in
      aux res (loaded_sz + 1) (Pointer.next ptr)
  in
  aux (BitVecVal.from_int ~len:1 0) 0 ptr

let load_as ptr repr mem =
  let load_size = MachineType.Repr.size_of repr in
  let value = load ptr load_size mem in
  value

(* Store [value] at block of [ptr] with the size [sz] *)
let store ptr sz cond value mem =
  let rec aux stored_sz value ptr mem =
    if stored_sz = sz then mem
    else
      let byte = BitVec.extract ((stored_sz * 8) + 7) (stored_sz * 8) value in
      let original = load ptr 1 mem in
      let updated_mem = Array.store (Bool.ite cond byte original) ptr mem in
      aux (stored_sz + 1) value (Pointer.next ptr) updated_mem
  in
  aux 0 value ptr mem

let store_as ptr repr cond value mem =
  let store_size = MachineType.Repr.size_of repr in
  store ptr store_size cond value mem
