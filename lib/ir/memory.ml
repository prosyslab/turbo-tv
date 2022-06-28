open Z3utils

type t = Array.t

let init name = Array.init name (BitVec.mk_sort 64) (BitVec.mk_sort 8)

let allocate bid size =
  bid := !bid + 1;
  TaggedPointer.init !bid size

(* Load [value] at block of [ptr] with the size [sz]*)
let load ptr sz mem =
  let rec aux res loaded_sz ptr =
    if loaded_sz = sz then res
    else
      let byte = Array.select ptr mem in
      let res = if loaded_sz = 0 then byte else BitVec.concat byte res in
      aux res (loaded_sz + 1) (TaggedPointer.next ptr)
  in
  aux (BitVecVal.from_int ~len:1 0) 0 ptr

let load_as ptr repr mem =
  let load_size = MachineType.Repr.size_of repr in
  load ptr load_size mem

(* Store [value] at block of [ptr] with the size [sz] *)
let store ptr sz cond value mem =
  let rec aux stored_sz value ptr mem =
    if stored_sz = sz then mem
    else
      let byte = BitVec.extract ((stored_sz * 8) + 7) (stored_sz * 8) value in
      let updated_mem = Array.store byte ptr mem in
      aux (stored_sz + 1) value (TaggedPointer.next ptr) updated_mem
  in
  Bool.ite cond (aux 0 value ptr mem) mem

let store_as ptr repr cond value mem =
  let store_size = MachineType.Repr.size_of repr in
  store ptr store_size cond value mem
