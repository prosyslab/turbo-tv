open Z3utils

type t = BitVec.t

(* 5-bit for type & 64-bit for data *)
let ty_len = Type.len
let data_len = 64
let len = ty_len + data_len

(* getter *)
let ty_of t = BitVec.extract (len - 1) data_len t
let data_of t = BitVec.extract (data_len - 1) 0 t

(* methods *)
let len_of t = BitVec.len t
let has_type ty t = BitVec.eqb (ty_of t) ty

let has_repr repr t =
  let tys_of_repr = Type.from_repr repr in
  Bool.ors (List.map (fun ty_candid -> has_type ty_candid t) tys_of_repr)

let cast ty t =
  if len_of t <> len then failwith "invalid value length"
  else BitVec.concat ty (data_of t)

let entype ty data =
  if len_of data <> data_len then failwith "invalid data length"
  else BitVec.concat ty data

let is_equal lval rval = BitVec.eqb lval rval
let is_weak_equal lval rval = BitVec.eqb (data_of lval) (data_of rval)

let can_be_smi bv =
  let data = data_of bv in
  Bool.ands [ BitVec.sgei data Type.smi_min; BitVec.slti data Type.smi_max ]

(* type-preserving binary operation *)
let add lval rval =
  let lty = ty_of lval in
  BitVec.addb (data_of lval) (data_of rval) |> entype lty

let lshr lval rval =
  let lty = ty_of lval in
  BitVec.lshrb (data_of lval) (data_of rval) |> entype lty

let ashr lval rval =
  let lty = ty_of lval in
  BitVec.ashrb (data_of lval) (data_of rval) |> entype lty

let mask lval rval =
  let lty = ty_of lval in
  BitVec.andb (data_of lval) (data_of rval) |> entype lty

(* constructor *)
let init name = BitVec.init ~len name
let from_int i = BitVecVal.of_int ~len i |> cast Type.const
let from_string s = BitVecVal.of_str ~len s |> cast Type.const
let from_bv bv = BitVec.zero_extend (len - BitVec.len bv) bv |> cast Type.const

(* constant values *)
let empty = BitVecVal.zero ~len () |> cast Type.undef
let tr = BitVecVal.tr ~len () |> cast Type.bool
let fl = BitVecVal.fl ~len () |> cast Type.bool

module Composed = struct
  type t = BitVec.t

  let init name = BitVec.init ~len:(len * 2) name
  let first_of t = BitVec.extract ((2 * len) - 1) len t
  let second_of t = BitVec.extract (len - 1) 0 t
end
