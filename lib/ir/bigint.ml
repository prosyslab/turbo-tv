open Z3utils
open ValueOperator
module FD = Z3.FuncDecl
module TP = ValueOperator.TaggedPointer

let length_length = 31

let sign_length = 1

let header_size = 4

let header_length = sign_length + length_length

let pos_sign = BitVecVal.from_int ~len:sign_length 0

let neg_sign = BitVecVal.from_int ~len:sign_length 1

let digit_size = 8

let digit_length = 8 * 8

type t = { map : BitVec.t; length : int; sign : BitVec.t; value : BitVec.t }

let num_digits t = BitVec.length_of t.value / digit_length

(* initialize *)
let create sign value = { map = Objmap.big_int_map; length = 1; sign; value }

let allocate t mem =
  let sign = t.sign in
  let size = num_digits t * digit_size in
  let ptr, mem =
    Memory.allocate (Value.from_int (Objmap.size + header_size + size)) mem
  in
  let big_int_value = t.value in
  let raw_ptr = ptr |> TaggedPointer.to_raw_pointer in
  let mem =
    mem
    |> Memory.store Bool.tr raw_ptr Objmap.size Objmap.big_int_map
    |> Memory.store Bool.tr
         (TaggedPointer.movei raw_ptr Objmap.size)
         header_size
         (BitVec.concat (BitVecVal.from_int 1 ~len:length_length) sign)
    |> Memory.store Bool.tr
         (TaggedPointer.movei raw_ptr (Objmap.size + header_size))
         size big_int_value
  in
  (ptr, mem)

let from_int i =
  let sign = BitVecVal.from_int ~len:sign_length (if i < 0 then 1 else 0) in
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
    |> BitVecVal.from_int ~len:sign_length
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
    BitVec.andi
      (Memory.load
         (TaggedPointer.movei ptr Objmap.size |> TaggedPointer.to_raw_pointer)
         header_size mem)
      1
    |> BitVec.extract 0 0
  in
  let value =
    Memory.load
      (TaggedPointer.movei ptr (Objmap.size + header_size)
      |> TaggedPointer.to_raw_pointer)
      8 mem
  in
  { map; length = 1; sign; value }

let extend t = { t with value = BitVec.zero_extend digit_length t.value }

let extend_n_digits n t =
  { t with value = BitVec.zero_extend (n * digit_length) t.value }

(* fit a to b *)
let fit a b =
  let a_num_digits = num_digits a in
  let b_num_digits = num_digits b in
  if a_num_digits > b_num_digits then
    (a, b |> extend_n_digits (a_num_digits - b_num_digits))
  else if a_num_digits < b_num_digits then
    (a |> extend_n_digits (b_num_digits - a_num_digits), b)
  else (a, b)

(* constants *)
let zero = create pos_sign (BitVecVal.zero ~len:(digit_size * 8) ())

(* check *)
let is_zero t = BitVec.eqb (BitVecVal.zero ~len:digit_length ()) t.value

let is_negative t =
  let sign = t.sign in
  BitVec.eqb neg_sign sign

let is_positive t =
  let sign = t.sign in
  BitVec.eqb pos_sign sign

let has_one_digit t = t |> num_digits = 1

(* conversion *)
let to_int64 t =
  Bool.ite (is_negative t) (BitVec.subb (BitVecVal.zero ()) t.value) t.value
  |> Value.entype Type.int64

(* comparison *)
let equal l r =
  let l, r = fit l r in
  Bool.ands [ Bool.eq l.sign r.sign; Bool.eq l.value r.value ]

let less_than l r =
  let l, r = fit l r in
  Bool.ite
    (Bool.ands [ l |> is_negative; r |> is_positive ])
    Bool.tr
    (Bool.ite
       (Bool.ands [ l |> is_positive; r |> is_negative ])
       Bool.fl
       (BitVec.ultb l.value r.value))

let less_than_or_equal l r = Bool.ors [ equal l r; less_than l r ]

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
        BitVec.mk_sort ((num_digits l * digit_length) + 1);
        BitVec.mk_sort ((num_digits r * digit_length) + 1);
      ]
      (BitVec.mk_sort 65)
  in

  (* Assume l and r only have one digit *)
  if (not (has_one_digit l)) || not (has_one_digit r) then
    create pos_sign
      (FD.apply approx [ l.value; r.value ]
      |> BitVec.extract (digit_length - 1) 0)
  else
    (* 1. apply sign and extend *)
    let l_value =
      let extended = l.value |> BitVec.zero_extend 1 in
      Bool.ite (is_negative l) (BitVec.neg extended) extended
    in
    let r_value =
      let extended = r.value |> BitVec.zero_extend 1 in
      Bool.ite (is_negative r) (BitVec.neg extended) extended
    in

    (* 2. check whether extension is required *)
    let can_overflow = Bool.not (BitVec.add_no_overflow l_value r_value true) in
    let can_underflow = Bool.not (BitVec.add_no_underflow l_value r_value) in
    let need_extension = Bool.ors [ can_overflow; can_underflow ] in

    (* 3. add *)
    let added = BitVec.addb l_value r_value in
    let sign = Bool.ite (BitVec.slti added 0) neg_sign pos_sign in
    let value =
      Bool.ite need_extension
        (FD.apply approx [ l_value; r_value ])
        (Bool.ite (Bool.eq sign neg_sign) (BitVec.neg added) added)
      |> BitVec.extract (digit_length - 1) 0
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
    create pos_sign (FD.apply approx [ l.value; r.value ])
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
      Bool.ite
        (Bool.ors
           [ Bool.eq l.sign r.sign; BitVec.eqi l.value 0; BitVec.eqi r.value 0 ])
        pos_sign neg_sign
    in
    let value =
      Bool.ite need_extension (FD.apply approx [ l_value; r_value ]) res
    in
    create sign value

let div l r =
  let approx =
    FD.mk_func_decl_s ctx "BigInt.div"
      [
        BitVec.mk_sort (num_digits l * digit_length);
        BitVec.mk_sort (num_digits r * digit_length);
      ]
      (BitVec.mk_sort 64)
  in

  (* Assume l and r only have one digit *)
  if (not (has_one_digit l)) || not (has_one_digit r) then
    create pos_sign (FD.apply approx [ l.value; r.value ])
  else
    let l_value = l.value in
    let r_value = r.value in

    let sign =
      Bool.ite
        (Bool.ors
           [ Bool.eq l.sign r.sign; BitVec.eqi l.value 0; BitVec.eqi r.value 0 ])
        pos_sign neg_sign
    in
    let value = BitVec.udivb l_value r_value in
    create sign value

let rem l r =
  let approx =
    FD.mk_func_decl_s ctx "BigInt.rem"
      [
        BitVec.mk_sort (num_digits l * digit_length);
        BitVec.mk_sort (num_digits r * digit_length);
      ]
      (BitVec.mk_sort 64)
  in

  (* Assume l and r only have one digit *)
  if (not (has_one_digit l)) || not (has_one_digit r) then
    create pos_sign (FD.apply approx [ l.value; r.value ])
  else
    let l_value = l.value in
    let r_value = r.value in

    let value = BitVec.modb l_value r_value in
    let sign = Bool.ite (BitVec.eqi value 0) pos_sign l.sign in
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

let shift_right v o =
  let approx =
    FD.mk_func_decl_s ctx "BigInt.right_shift"
      [
        BitVec.mk_sort (num_digits v * digit_length);
        BitVec.mk_sort (num_digits o * digit_length);
      ]
      (BitVec.mk_sort 64)
  in
  if (not (has_one_digit v)) || not (has_one_digit o) then
    create pos_sign (FD.apply approx [ v.value; o.value ])
  else
    let value = BitVec.lshrb v.value o.value in
    { v with value }

let bigint_bitwise op l r =
  let op =
    match op with
    | "&" -> BitVec.andb
    | "|" -> BitVec.orb
    | "^" -> BitVec.xor
    | _ -> failwith "unreachable"
  in

  let l_value =
    let extended = l.value |> BitVec.zero_extend 1 in
    Bool.ite (is_negative l) (BitVec.neg extended) extended
  in
  let r_value =
    let extended = r.value |> BitVec.zero_extend 1 in
    Bool.ite (is_negative r) (BitVec.neg extended) extended
  in

  let res = op l_value r_value in
  let sign = Bool.ite (BitVec.slti res 0) neg_sign pos_sign in
  let value =
    Bool.ite (Bool.eq sign neg_sign) (BitVec.neg res) res
    |> BitVec.extract (digit_length - 1) 0
  in
  create sign value

let bitwise_and l r = bigint_bitwise "&" l r

let bitwise_or l r = bigint_bitwise "|" l r

let bitwise_xor l r = bigint_bitwise "^" l r

(* stringify *)
let to_string model t =
  let sign_str =
    if
      BitVec.eqi t.sign 0 |> Model.eval model |> Expr.to_simplified_string
      = "true"
    then "+"
    else "-"
  in
  let value_str =
    t.value |> BitVec.to_uint |> Model.eval model |> Expr.to_simplified_string
  in
  Format.sprintf "BigInt(%s)" (sign_str ^ value_str)

let to_bytestring model t =
  let map_bs = t.map |> Model.eval model |> Expr.to_string in
  let sign_bs = t.sign |> Model.eval model |> Expr.to_string in
  let value_bs = t.value |> Model.eval model |> Expr.to_string in
  String.concat " " [ map_bs; sign_bs; value_bs ]
