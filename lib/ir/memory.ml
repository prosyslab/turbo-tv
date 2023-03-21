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
    print_endline "In Memory.Bytes.load";
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
  (* let load ptr sz t =
     print_endline "In Memory.Strings.load";
     let str =
       Array.select
         (BitVec.ori
            (BitVec.shli (TaggedPointer.bid_of ptr |> BitVec.zero_extend 24) 24)
            4)
         t.strings
     in
     Seq.extract str
       (ptr |> TaggedPointer.off_of |> Expr.to_simplified_string
      |> Seq.from_string |> Seq.string_to_int)
       (sz |> string_of_int |> Seq.from_string |> Seq.string_to_int) *)

  (* let load_as ptr repr mem =
     let load_size = MachineType.Repr.size_of repr in
     load ptr load_size mem *)

  let load ptr t =
    print_endline "In Memory.Strings.load";
    print_endline
      (Array.select ptr t.strings |> Expr.get_sort |> Z3.Sort.to_string);
    (* print_endline (Array.select ptr t.strings |> Seq.is_string |> string_of_bool); *)
    (* print_endline (Array.select ptr t.strings |> Seq.get_string); *)
    Array.select ptr t.strings

  let load_as ptr mem = load ptr mem

  let store cond ptr value t =
    print_endline "In Memory.Strings.store";
    let updated_mem =
      Bool.ite cond (Array.store value ptr t.strings) t.strings
    in
    { t with strings = updated_mem }

  let store_as cond ptr _ value mem = store cond ptr value mem
end

module Objects = struct
  let map_of ptr mem =
    print_endline
      (Bytes.load (ptr |> TaggedPointer.to_raw_pointer) 4 mem
      |> Expr.to_simplified_string);
    Bytes.load (ptr |> TaggedPointer.to_raw_pointer) 4 mem
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
    (* print_endline (ptr |> Expr.to_simplified_string);
       print_endline (TaggedPointer.bid_of ptr |> Expr.to_simplified_string);
       print_endline
         (BitVec.shli (BitVec.zero_extend 24 (TaggedPointer.bid_of ptr)) 24
         |> Expr.to_simplified_string);
       Bool.ands
         [
           BitVec.shli (TaggedPointer.bid_of ptr |> BitVec.zero_extend 24) 24
           |> Value.has_type Type.tagged_pointer;
           BitVec.shli (TaggedPointer.bid_of ptr |> BitVec.zero_extend 24) 24
           |> has_map_of Objmap.string_map mem;
         ] *)
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
    Array.init "string_mem" (BitVec.mk_sort TaggedPointer.ptr_len) Seq.mk_sort
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

let load ptr sz mem =
  print_endline "In Memory.load";
  print_endline "check map";

  print_endline (ptr |> Expr.to_simplified_string);
  (* print_endline
       (BitVec.addi
          (BitVec.shli (TaggedPointer.bid_of ptr |> BitVec.zero_extend 24) 24)
          1
       |> Expr.to_simplified_string); *)
  print_endline "check if";
  print_endline
    (BitVec.addi (TaggedPointer.off_of ptr) 1
    |> BitVec.zero_extend 8 |> Int32.is_zero |> Expr.simplify None |> B.is_true
    |> string_of_bool);
  (* print_endline
     (BitVec.addi
        (BitVec.shli (TaggedPointer.bid_of ptr |> BitVec.zero_extend 24) 24)
        1
     |> Objects.has_map_of Objmap.string_map mem
     |> Expr.to_simplified_string); *)
  if
    BitVec.addi (TaggedPointer.off_of ptr) 1
    |> BitVec.zero_extend 8 |> Int32.is_zero |> Expr.simplify None |> B.is_true
    = true
  then Bytes.load ptr sz mem
  else if
    BitVec.addi
      (BitVec.shli (TaggedPointer.bid_of ptr |> BitVec.zero_extend 24) 24)
      1
    |> Objects.has_map_of Objmap.string_map mem
    |> Expr.simplify None |> B.is_true = true
    (* then Strings.load ptr sz mem *)
  then Strings.load ptr mem
  else Bytes.load ptr sz mem

let load_as ptr repr mem =
  (* print_endline "check map";

     print_endline (ptr |> Expr.to_simplified_string);
     print_endline
       (BitVec.addi
          (BitVec.shli (TaggedPointer.bid_of ptr |> BitVec.zero_extend 24) 24)
          1
       |> Expr.to_simplified_string);
     print_endline "check if";
     print_endline
       (BitVec.addi (TaggedPointer.off_of ptr) 1 |> Expr.to_simplified_string);
     print_endline
       (BitVec.addi
          (BitVec.shli (TaggedPointer.bid_of ptr |> BitVec.zero_extend 24) 24)
          1
       |> Objects.has_map_of Objmap.string_map mem
       |> Expr.to_simplified_string); *)
  if BV.is_bv_zeroextension (BitVec.addi (TaggedPointer.off_of ptr) 1) = true
  then Bytes.load_as ptr repr mem
  else if
    BitVec.addi
      (BitVec.shli (TaggedPointer.bid_of ptr |> BitVec.zero_extend 24) 24)
      1
    |> Objects.has_map_of Objmap.string_map mem
    |> Expr.simplify None |> B.is_true = true
    (* then Strings.load_as ptr repr mem *)
  then Strings.load_as ptr mem
  else Bytes.load_as ptr repr mem

let store cond ptr sz value t =
  print_endline "In Memory.store";
  print_endline (ptr |> Expr.to_simplified_string);
  if value |> Seq.is_string = true then Strings.store cond ptr value t
  else Bytes.store cond ptr sz value t

let store_as cond ptr repr value mem =
  if value |> Seq.is_string = true then Strings.store cond ptr value mem
  else
    let store_size = MachineType.Repr.size_of repr in
    Bytes.store cond ptr store_size value mem

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
