open Z3utils
open ValueOperator

type t = {
  bytes : Array.t;
  bsizes : Array.t;
  is_angelic : Array.t;
  next_bid : int;
}

let byte_size = 1

let byte_len = byte_size * 8

let max_size_per_block = byte_size * 3

let max_len_per_block = byte_len * 3

let init nparams =
  let bytes =
    Array.init "mem"
      (BitVec.mk_sort TaggedPointer.ptr_len)
      (BitVec.mk_sort byte_len)
  in
  let bsizes =
    Array.init "size_map"
      (BitVec.mk_sort TaggedPointer.bid_len)
      (BitVec.mk_sort TaggedPointer.off_len)
  in
  let is_angelic =
    Z3.Z3Array.mk_const_array ctx (BitVec.mk_sort TaggedPointer.bid_len) Bool.tr
  in
  { bytes; bsizes; is_angelic; next_bid = nparams + 1 }

let allocate ?(angelic = Bool.fl) size t =
  let size =
    Bool.ite
      (size |> Value.has_type Type.float64)
      (size |> Float64.to_uint32)
      size
    |> BitVec.extract (max_len_per_block - 1) 0
  in
  let bid = t.next_bid |> BitVecVal.from_int ~len:TaggedPointer.bid_len in
  let memory =
    {
      t with
      bsizes = Array.store size bid t.bsizes;
      is_angelic = Array.store angelic bid t.is_angelic;
      next_bid = t.next_bid + 1;
    }
  in
  (TaggedPointer.init bid, memory)

let size_of bid t = Array.select bid t.bsizes

(* Load [value] at block of [ptr] with the size [sz]*)
let load ptr sz t =
  let rec aux res loaded_sz ptr =
    if loaded_sz = sz then res
    else
      let byte = Array.select ptr t.bytes in
      let res = if loaded_sz = 0 then byte else BitVec.concat byte res in
      aux res (loaded_sz + 1) (TaggedPointer.next ptr)
  in
  aux (BitVecVal.from_int ~len:1 0) 0 ptr

let load_as ptr repr mem =
  let load_size = MachineType.Repr.size_of repr in
  load ptr load_size mem

(* Store [value] at block of [ptr] with the size [sz] *)
let store cond ptr sz value t =
  let rec aux stored_sz value ptr bytes =
    if stored_sz = sz then bytes
    else
      let byte = BitVec.extract ((stored_sz * 8) + 7) (stored_sz * 8) value in
      aux (stored_sz + 1) value (TaggedPointer.next ptr)
        (Array.store byte ptr bytes)
  in
  let updated_mem = Bool.ite cond (aux 0 value ptr t.bytes) t.bytes in
  { t with bytes = updated_mem }

let store_as cond ptr repr value mem =
  let store_size = MachineType.Repr.size_of repr in
  store cond ptr store_size value mem

let can_access ptr sz t =
  (* no out-of-bounds *)
  let bid = TaggedPointer.bid_of ptr in
  let off = TaggedPointer.off_of ptr in
  let bsize = size_of bid t in
  let out_of_lb = BitVec.slti off 0 in
  let out_of_ub = BitVec.ugtb (BitVec.addi off sz) bsize in
  Bool.ite
    (Array.select bid t.is_angelic)
    Bool.tr
    (Bool.not (Bool.ors [ out_of_lb; out_of_ub ]))

(* can read as [repr] *)
let can_access_as ptr repr t =
  let repr_sz = MachineType.Repr.size_of repr in
  can_access ptr repr_sz t
