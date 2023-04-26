open Z3utils
open ValueOperator

type t = {
  bytes : Array.t;
  bsizes : Array.t;
  is_angelic : Array.t;
  strings : Array.t;
  next_bid : int;
}

let byte_size = 1

let byte_len = byte_size * 8

let max_size_per_block = byte_size * 3

let max_len_per_block = byte_len * 3

let size_of bid t = Array.select bid t.bsizes

module Bytes = struct
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
end

module Strings = struct
  let load ptr t = Array.select ptr t.strings

  let store cond ptr value t =
    let updated_mem =
      Bool.ite cond (Array.store value ptr t.strings) t.strings
    in
    { t with strings = updated_mem }
end

module Objects = struct
  let map_of ptr mem = Bytes.load (ptr |> TaggedPointer.to_raw_pointer) 4 mem
  (* let map_of ptr mem = Bytes.load ptr 4 mem *)

  let has_map_of map mem ptr = Bool.eq (map_of ptr mem) map

  let is_big_int mem ptr =
    Bool.ands
      [
        ptr |> Value.has_type Type.tagged_pointer;
        ptr |> has_map_of Objmap.big_int_map mem;
      ]

  let is_boolean mem ptr =
    Bool.ands
      [
        ptr |> Value.has_type Type.tagged_pointer;
        ptr |> has_map_of Objmap.boolean_map mem;
      ]

  let is_heap_number mem ptr =
    Bool.ands
      [
        ptr |> Value.has_type Type.tagged_pointer;
        ptr |> has_map_of Objmap.heap_number_map mem;
      ]

  let is_null mem ptr =
    Bool.ands
      [
        ptr |> Value.has_type Type.tagged_pointer;
        ptr |> has_map_of Objmap.null_map mem;
      ]

  let is_undefined mem ptr =
    Bool.ands
      [
        ptr |> Value.has_type Type.tagged_pointer;
        ptr |> has_map_of Objmap.undefined_map mem;
      ]

  let is_string mem ptr =
    Bool.ands
      [
        ptr |> Value.has_type Type.tagged_pointer;
        ptr |> has_map_of Objmap.string_map mem;
      ]

  let are_heap_nubmer mem ptrs =
    Bool.ands (List.map (has_map_of Objmap.heap_number_map mem) ptrs)
end

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
  let strings =
    Array.init "string_mem" (BitVec.mk_sort TaggedPointer.ptr_len) Str.sort
  in
  { bytes; bsizes; is_angelic; strings; next_bid = nparams + 1 }

let is_angelic t v =
  let bid = TaggedPointer.bid_of v in
  Array.select bid t.is_angelic

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

let can_access ptr sz t =
  (* no out-of-bounds *)
  let bid = TaggedPointer.bid_of ptr in
  let off = TaggedPointer.off_of ptr in
  let bsize = size_of bid t in
  let lb_access_check = BitVec.sgei off 0 in
  let ub_access_check = BitVec.sleb (BitVec.addi off sz) bsize in
  Bool.ite
    (Array.select bid t.is_angelic)
    Bool.tr
    (Bool.ands [ lb_access_check; ub_access_check ])

(* can read as [repr] *)
let can_access_as ptr repr t =
  let repr_sz = MachineType.Repr.size_of repr in
  can_access ptr repr_sz t

let equal m1 m2 =
  (* type t = {
       bytes : Array.t;
       bsizes : Array.t;
       is_angelic : Array.t;
       strings : Array.t;
       next_bid : int;
     } *)
  Bool.ands
    [
      Bool.eq m1.bytes m2.bytes;
      Bool.eq m1.bsizes m2.bsizes;
      Bool.eq m1.is_angelic m2.is_angelic;
      Bool.eq m1.strings m2.strings;
    ]
