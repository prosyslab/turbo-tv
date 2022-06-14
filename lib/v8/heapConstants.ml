open Z3utils

let undefined_constant bid mem =
  let ptr = Memory.allocate bid (BitVecVal.from_int ~len:Value.len 1) in
  (ptr, Memory.store ptr 1 Bool.tr (BitVecVal.from_int 0) mem)

let the_hole_constant bid mem =
  let ptr = Memory.allocate bid (BitVecVal.from_int ~len:Value.len 1) in
  (ptr, Memory.store ptr 1 Bool.tr (BitVecVal.from_int 0) mem)

let null_constant bid mem =
  let ptr = Memory.allocate bid (BitVecVal.from_int ~len:Value.len 1) in
  (ptr, Memory.store ptr 1 Bool.tr (BitVecVal.from_int 0) mem)

let empty_string_constant bid mem =
  let ptr = Memory.allocate bid (BitVecVal.from_int ~len:Value.len 1) in
  (ptr, Memory.store ptr 1 Bool.tr (BitVecVal.from_int 0) mem)

let false_constnat bid mem =
  let ptr = Memory.allocate bid (BitVecVal.from_int ~len:Value.len 1) in
  Memory.store ptr 1 Bool.tr (BitVecVal.from_int 0) mem

let true_constant bid mem =
  let ptr = Memory.allocate bid (BitVecVal.from_int ~len:Value.len 1) in
  Memory.store ptr 1 Bool.tr (BitVecVal.from_int 0) mem
