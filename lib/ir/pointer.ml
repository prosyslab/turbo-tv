open Z3utils

type t = Value.t

let next_bid = ref 1

(* const *)
(* 0-15: offset
   16-47: bid
   48-63: size of struct
   64-68: value type(Pointer)
   69-70: undef
*)
(* High |u|-ty-|--sz--|--bid--|-offset-| Low *)
let size_len = 16
let bid_len = 32
let off_len = 16
let len = Value.len

(* getter *)
let size_of t =
  BitVec.extract (size_len + bid_len + off_len - 1) (bid_len + off_len) t

let bid_of t = BitVec.extract (bid_len + off_len - 1) off_len t
let off_of t = BitVec.extract (off_len - 1) 0 t

(* constructor *)
let init vid sz =
  let ptr = Value.init vid in
  let bid = BitVecVal.of_int ~len:64 !next_bid in
  let sz = Value.data_of sz in
  let value =
    BitVec.orb (BitVec.shli sz (bid_len + off_len)) (BitVec.shli bid off_len)
    |> Value.entype Type.pointer
  in
  (ptr, BitVec.eqb ptr value)

(* method *)
let next t = BitVec.addi t 1
let move t pos = BitVec.addb t pos

let can_access pos sz t =
  (* no out-of-bounds *)
  let struct_size = Value.from_bv (size_of t) in
  let out_of_lb = Value.slt pos (0 |> Value.from_int) in
  let out_of_ub = Value.uge (BitVec.addi pos sz) struct_size in
  Bool.ands [ Bool.not out_of_lb; Bool.not out_of_ub ]

(* can read as [repr] *)
let can_access_as pos repr t =
  let repr_sz = MachineType.Repr.size_of repr in
  can_access pos repr_sz t
