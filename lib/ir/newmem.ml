open Z3utils
open ValueOperator

type t = { maps : Array.t; values : Array.t; next_bid : int }

let map_size = 4

let init nparams =
  print_endline "In Newmem.init";
  let maps = 
    Array.init "string_map" (BitVec.mk_sort TaggedPointer.ptr_len) (BitVec.mk_sort 8) in
  let values =
    Array.init "string_mem" (BitVec.mk_sort TaggedPointer.ptr_len) Seq.mk_sort
  in
  { maps; values; next_bid = nparams + 1 }

let allocate t =
  print_endline "In Newmem.allocate"; 
  let bid = t.next_bid |> BitVecVal.from_int ~len:TaggedPointer.bid_len in
  let memory = { t with next_bid = t.next_bid + 1 } in
  (TaggedPointer.init bid, memory)

let load ptr t = 
  print_endline "In Newmem.load"; 
  Array.select ptr t.values


let  store_map cond ptr value t =
  print_endline "In Newmem.store_map";
  let updated_mem = Bool.ite cond (Array.store value ptr t.maps) t.maps in
  {t with maps = updated_mem}

let store_string cond ptr value t =
  print_endline "In Newmem.store_string";
  let updated_mem = Bool.ite cond (Array.store value ptr t.values) t.values in
  {t with values = updated_mem}