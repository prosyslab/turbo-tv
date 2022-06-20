open Z3utils

type t = Value.t

(* const *)
(* 0-16: offset
   16-48: bid
   48-64: size of struct
   64-69: value type(Pointer)
*)
(* High |-ty-|--sz--|--bid--|-offset-| Low *)
let size_len = 16

let bid_len = 32

let off_len = 16

let len = Value.len

let size = Value.size

(* getter *)
let size_of t =
  BitVec.extract (size_len + bid_len + off_len - 1) (bid_len + off_len) t

let bid_of t = BitVec.extract (bid_len + off_len - 1) off_len t

let off_of t = BitVec.extract (off_len - 1) 0 t

(* constructor *)
let init bid sz =
  let bid = BitVecVal.from_int ~len:64 bid in
  let sz = Value.data_of sz in
  let value =
    BitVec.orb (BitVec.shli sz (bid_len + off_len)) (BitVec.shli bid off_len)
    |> Value.entype Type.tagged_pointer
  in
  value

(* method *)
let next t = BitVec.addi t 1

let move t pos = BitVec.addb t pos

let movei t pos = BitVec.addi t pos

let can_access pos sz t =
  (* no out-of-bounds *)
  let struct_size = Value.from_bv (size_of t) in
  let out_of_lb = Value.slt pos (0 |> Value.from_int) in
  let out_of_ub = Value.uge (Value.addi pos sz) struct_size in
  Bool.not (Bool.ors [ out_of_lb; out_of_ub ])

(* can read as [repr] *)
let can_access_as pos repr t =
  let repr_sz = MachineType.Repr.size_of repr in
  can_access pos repr_sz t

let to_string model t =
  let bid =
    let bid_str = bid_of t |> Model.eval model |> Expr.to_string in
    "0" ^ String.sub bid_str 1 (String.length bid_str - 1)
    |> Int32.of_string |> Int32.unsigned_to_int |> Option.get
  in
  let offset =
    let off_str = off_of t |> Model.eval model |> Expr.to_string in
    "0" ^ String.sub off_str 1 (String.length off_str - 1)
    |> Int32.of_string |> Int32.unsigned_to_int |> Option.get
  in

  Format.sprintf "Pointer(bid: %d, offset: %d)" bid offset
