open Z3utils
open ValueOperator
module FD = Z3.FuncDecl
module TP = ValueOperator.TaggedPointer

let sign_size = 1

let sign_length = 1 * 8

let pos_sign = BitVecVal.from_int ~len:sign_length 0

let neg_sign = BitVecVal.from_int ~len:sign_length 1

let digit_size = 8

let digit_length = 8 * 8

type t = { map : BitVec.t; sign : BitVec.t; value : BitVec.t }

let num_digits t = BitVec.length_of t.value / digit_length

(* initialize *)
let create sign value = { map = Objmap.big_int_map; sign; value }

let allocate t mem =
  let sign = t.sign in
  let size = num_digits t * 8 in
  let ptr, mem =
    Memory.allocate (Value.from_int (Objmap.size + sign_size + size)) mem
  in
  let big_int_value = t.value in
  let mem =
    mem
    |> Memory.store Bool.tr
         (ptr |> TaggedPointer.to_raw_pointer)
         Objmap.size Objmap.big_int_map
    |> Memory.store Bool.tr
         (TaggedPointer.movei ptr Objmap.size |> TaggedPointer.to_raw_pointer)
         sign_size sign
    |> Memory.store Bool.tr
         (TaggedPointer.movei ptr (Objmap.size + sign_size)
         |> TaggedPointer.to_raw_pointer)
         size big_int_value
  in
  (ptr, mem)

let from_int i =
  let sign = BitVecVal.from_int ~len:8 (if i < 0 then 1 else 0) in
  let value =
    (* abs(i) returns negative value when i is Int.min_int *)
    if i <> Int.min_int then BitVecVal.from_int ~len:64 (abs i)
    else BitVecVal.from_int ~len:64 i |> BitVec.neg
  in
  create sign value

let from_string s =
  let sign_and_values = s |> String.split_on_char ' ' |> List.tl in
  let sign =
    (if String.equal (List.hd sign_and_values) "+" then 0 else 1)
    |> BitVecVal.from_int ~len:8
  in
  let values = List.tl sign_and_values in

  (* each value in values is 64-bit value *)
  let value =
    values
    |> List.map (fun s -> BitVecVal.from_istring_trunc s)
    |> Composed.from_values
  in
  create sign value

let load ptr mem =
  let map = Memory.load (ptr |> TaggedPointer.to_raw_pointer) Objmap.size mem in
  let sign =
    Memory.load
      (TaggedPointer.movei ptr Objmap.size |> TaggedPointer.to_raw_pointer)
      sign_size mem
  in
  let value =
    Memory.load
      (TaggedPointer.movei ptr (Objmap.size + sign_size)
      |> TaggedPointer.to_raw_pointer)
      8 mem
  in
  { map; sign; value }

let extend t = { t with value = BitVec.zero_extend digit_length t.value }

let extend_n_digits n t =
  { t with value = BitVec.zero_extend (n * digit_length) t.value }

let extend_to n t =
  let len = BitVec.length_of t.value in
  if len < n * digit_length then
    { t with value = BitVec.zero_extend ((n * digit_length) - len) t.value }
  else t

(* constants *)
let zero = create pos_sign (BitVecVal.zero ~len:(digit_size * 8) ())

(* check *)
let is_zero t = BitVec.eqb (BitVecVal.zero ~len:digit_length ()) t.value

let is_negative t =
  let sign = t.sign in
  BitVec.eqb neg_sign sign

let has_one_digit t = t |> num_digits = 1

(* conversion *)
let to_int64 t =
  Bool.ite (is_negative t) (BitVec.subb (BitVecVal.zero ()) t.value) t.value
  |> Value.entype Type.int64

(* comparison *)
let equal l r = Bool.ands [ Bool.eq l.sign r.sign; Bool.eq l.value r.value ]

(* arithmetic *)
let neg v =
  {
    v with
    sign = Bool.ite (Bool.ors [ is_negative v; is_zero v ]) pos_sign neg_sign;
  }

let add l r =
  let approx =
    FD.mk_func_decl_s ctx "BigInt.add"
      [
        BitVec.mk_sort (num_digits l * digit_length);
        BitVec.mk_sort (num_digits r * digit_length);
      ]
      (BitVec.mk_sort 64)
  in

  (* Assume l and r only have one digit *)
  if (not (has_one_digit l)) || not (has_one_digit r) then
    create
      (BitVecVal.zero ~len:sign_length ())
      (FD.apply approx [ l.value; r.value ])
  else
    (* 1. apply sign and extend *)
    let l_value = Bool.ite (is_negative l) (BitVec.neg l.value) l.value in
    let r_value = Bool.ite (is_negative r) (BitVec.neg r.value) r.value in

    (* 2. check whether extension is required *)
    let can_overflow = Bool.not (BitVec.add_no_overflow l_value r_value true) in
    let can_underflow = Bool.not (BitVec.add_no_underflow l_value r_value) in
    let need_extension = Bool.ors [ can_overflow; can_underflow ] in

    (* 3. add *)
    let added = BitVec.addb l_value r_value in
    let sign =
      Bool.ite (BitVec.sltb added (BitVecVal.zero ())) neg_sign pos_sign
    in
    let value =
      Bool.ite need_extension
        (FD.apply approx [ l_value; r_value ])
        (Bool.ite (Bool.eq sign neg_sign) (BitVec.neg added) added)
    in
    create sign value

let sub l r = add l (neg r)

let mul l r =
  let approx =
    FD.mk_func_decl_s ctx "BigInt.mul"
      [
        BitVec.mk_sort (num_digits l * digit_length);
        BitVec.mk_sort (num_digits r * digit_length);
      ]
      (BitVec.mk_sort 64)
  in

  (* Assume l and r only have one digit *)
  if (not (has_one_digit l)) || not (has_one_digit r) then
    create
      (BitVecVal.zero ~len:sign_length ())
      (FD.apply approx [ l.value; r.value ])
  else
    let l_value = l.value in
    let r_value = r.value in

    (* 1. check whether extension is required *)
    let need_extension =
      Bool.not (BitVec.mul_no_overflow l_value r_value false)
    in

    (* 2. multiply *)
    let res = BitVec.mulb l_value r_value in
    let sign =
      Bool.ite (Bool.eq l.sign r.sign)
        (BitVecVal.zero ~len:sign_length ())
        (BitVecVal.from_int ~len:sign_length 1)
    in
    let value =
      Bool.ite need_extension (FD.apply approx [ l_value; r_value ]) res
    in
    create sign value

(* bitwise *)
let shift_left v o =
  let approx =
    FD.mk_func_decl_s ctx "BigInt.left_shift"
      [
        BitVec.mk_sort (num_digits v * digit_length);
        BitVec.mk_sort (num_digits o * digit_length);
      ]
      (BitVec.mk_sort 64)
  in
  if (not (has_one_digit v)) || not (has_one_digit o) then
    create pos_sign (FD.apply approx [ v.value; o.value ])
  else
    let shift_out =
      BitVec.andb v.value
        (BitVec.rorb
           (BitVec.subi
              (BitVec.shlb (BitVecVal.from_int ~len:digit_length 1) o.value)
              1)
           o.value)
    in
    let ovf = Bool.not (BitVec.eqb shift_out (BitVecVal.zero ())) in
    (* if there is overflow, we ignore the result and apply uif *)
    let value =
      Bool.ite ovf
        (FD.apply approx [ v.value; o.value ])
        (BitVec.shlb v.value o.value)
    in
    { v with value }

(* stringify *)
let to_string model t =
  let sign_str =
    if BitVec.eqi t.sign 0 |> Model.eval model |> Expr.to_string = "true" then
      "+"
    else "-"
  in
  let value_str =
    t.value |> BitVec.to_uint |> Model.eval model |> Expr.to_simplified_string
  in
  sign_str ^ value_str

let to_bytestring model t =
  let map_bs = t.map |> Model.eval model |> Expr.to_string in
  let sign_bs = t.sign |> Model.eval model |> Expr.to_string in
  let value_bs = t.value |> Model.eval model |> Expr.to_string in
  String.concat " " [ map_bs; sign_bs; value_bs ]
