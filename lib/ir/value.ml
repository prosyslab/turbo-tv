open Z3utils

type t = BitVec.t

(* 1-bit for undef & 5-bit for type & 64-bit for data *)
let undef_len = 1
let ty_len = Type.len
let data_len = 64
let len = undef_len + ty_len + data_len

(* getter *)
let ty_of t = BitVec.extract (data_len + ty_len - 1) data_len t
let data_of t = BitVec.extract (data_len - 1) 0 t
let undef_of t = BitVec.extract (len - 1) (len - 1) t

(* cast value [t] to type [ty] *)
let cast ty t =
  if BitVec.len t <> len then (
    BitVec.len t |> string_of_int |> print_endline;
    failwith "invalid value length")
  else
    let undef = undef_of t in
    BitVec.concat undef (BitVec.concat ty (data_of t))

(* entype [data] to type [ty] *)
let entype ty data =
  if BitVec.len data <> data_len then failwith "invalid data length"
    (* TODO handling undef of data *)
  else BitVec.concat (BitVecVal.zero ~len:1 ()) (BitVec.concat ty data)

(* constructor *)
let init name = BitVec.init ~len name
let from_int i = BitVecVal.of_int ~len i |> cast Type.const
let from_string s = BitVecVal.of_str ~len s |> cast Type.const
let from_bv bv = BitVec.zero_extend (len - BitVec.len bv) bv |> cast Type.const

(* methods *)
let has_type ty t = BitVec.eqb (ty_of t) ty

let has_repr repr t =
  let tys_of_repr = Type.from_repr repr in
  Bool.ors (List.map (fun ty_candid -> has_type ty_candid t) tys_of_repr)

let is_equal lval rval = BitVec.eqb lval rval
let is_weak_equal lval rval = BitVec.eqb (data_of lval) (data_of rval)

let can_be_smi bv =
  let data = data_of bv in
  Bool.ands [ BitVec.sgei data Type.smi_min; BitVec.slti data Type.smi_max ]

(* type-preserving binary operation *)
let add lval rval =
  let lty = ty_of lval in
  BitVec.addb (data_of lval) (data_of rval) |> entype lty

let slt lval rval = BitVec.sltb (data_of lval) (data_of rval)
let uge lval rval = BitVec.ugeb (data_of lval) (data_of rval)

let lshr lval rval =
  let lty = ty_of lval in
  BitVec.lshrb (data_of lval) (data_of rval) |> entype lty

let ashr lval rval =
  let lty = ty_of lval in
  BitVec.ashrb (data_of lval) (data_of rval) |> entype lty

let mask lval rval =
  let lty = ty_of lval in
  BitVec.andb (data_of lval) (data_of rval) |> entype lty

(* constant values *)
let empty = BitVecVal.zero ~len () |> cast Type.empty
let tr = BitVecVal.tr ~len () |> cast Type.bool
let fl = BitVecVal.fl ~len () |> cast Type.bool
let undefined = BitVec.lshri (BitVecVal.of_int ~len 1) (ty_len + data_len)
let is_undef t = BitVec.andb t undefined
let set_undef value = BitVec.orb undefined value
let clear_undef value = BitVec.andb (BitVec.notb undefined) value

module Composed = struct
  type t = BitVec.t

  let init name size = BitVec.init ~len:(len * size) name
  let size_of t = BitVec.len t / len

  let select idx t =
    let size = size_of t in
    BitVec.extract (((size - idx) * len) - 1) ((size - idx - 1) * len) t

  let first_of t = select 0 t
  let second_of t = select 1 t
end
