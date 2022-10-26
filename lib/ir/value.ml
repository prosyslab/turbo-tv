open Z3utils
module Repr = MachineType.Repr

type t = BitVec.t

(*  5-bit for type & 64-bit for data *)

let ty_len = Type.len

let data_len = 64

let len = ty_len + data_len

(* getter *)
let ty_of t = BitVec.extract (data_len + ty_len - 1) data_len t

let data_of t = BitVec.extract (data_len - 1) 0 t

(* cast value [t] to type [ty] *)
let cast ty t =
  if BitVec.length_of t <> len then (
    BitVec.length_of t |> string_of_int |> print_endline;
    failwith "invalid value length")
  else BitVec.concat ty (data_of t)

(* entype [data] to type [ty] *)
let entype ty data =
  let input_data_len = BitVec.length_of data in
  if input_data_len <> data_len then
    failwith (Printf.sprintf "invalid data length: %d" input_data_len)
  else BitVec.concat ty data

(* type checks *)
let rec has_type (ty : Type.t) t =
  if ty = Type.any_tagged then
    Bool.ors
      [ t |> has_type Type.tagged_pointer; t |> has_type Type.tagged_signed ]
  else if ty = Type.tagged_signed then
    Bool.ands [ BitVec.eqb (ty_of t) ty; BitVec.eqi (BitVec.andi t 1) 0 ]
  else if ty = Type.tagged_pointer then
    Bool.ands [ BitVec.eqb (ty_of t) ty; BitVec.eqi (BitVec.andi t 1) 1 ]
  else BitVec.eqb (ty_of t) ty

let is_32bit_integer t =
  Bool.ors [ t |> has_type Type.int32; t |> has_type Type.uint32 ]

let is_signed_integer t =
  Bool.ors (List.map (fun ty -> has_type ty t) Type.int_types)

let is_unsigned_integer t =
  Bool.ors (List.map (fun ty -> has_type ty t) Type.uint_types)

let is_integer t =
  Bool.ors
    [
      t |> has_type Type.tagged_signed;
      is_signed_integer t;
      is_unsigned_integer t;
    ]

let is_float t = Bool.ors (List.map (fun ty -> has_type ty t) Type.float_types)

(* constructor *)
let init name = BitVec.init ~len name

let from_int i = BitVecVal.from_int ~len i |> cast Type.const

let from_f64string s = BitVecVal.from_f64string s |> entype Type.const

let from_bv bv =
  BitVec.zero_extend (len - BitVec.length_of bv) bv |> cast Type.const

let empty = from_int 0 |> cast Type.empty

(* representation *)
let has_repr repr t =
  let tys_of_repr = Type.from_repr repr in
  Bool.ors (List.map (fun ty_candid -> has_type ty_candid t) tys_of_repr)

(* compare two values and return bool *)
let eq lval rval = BitVec.eqb lval rval

let weak_eq ?(repr = Repr.Word64) lval rval =
  let width = Repr.width_of repr in
  BitVec.eqb
    (BitVec.extract (width - 1) 0 lval)
    (BitVec.extract (width - 1) 0 rval)

let fl = empty |> cast Type.bool

let is_false value = weak_eq ~repr:Repr.Word32 fl value

let tr = BitVec.addi empty 1 |> cast Type.bool

let is_true value = Bool.not (is_false value)

let undefined = empty |> cast Type.undefined

let is_undefined value = eq undefined value
