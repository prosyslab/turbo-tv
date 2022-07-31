open Err
module A = Z3.Z3Array
module B = Z3.Boolean
module E = Z3.Expr
module M = Z3.Model
module AR = Z3.Arithmetic
module I = Z3.Arithmetic.Integer
module R = Z3.Arithmetic.Real
module S = Z3.Solver
module BV = Z3.BitVector
module Fl = Z3.FloatingPoint
module T = Z3.Tactic

(* global context *)
let ctx = Z3.mk_context [ ("model", "true") ]

(* default bitvector length *)
let bvlen = ref 64

let float_sort = ref (Fl.mk_sort_double ctx)

let set_bvlen len = bvlen := len

let set_float_sort sort = float_sort := sort

module Expr = struct
  (* print *)
  let simplify opt exp = E.simplify exp opt

  let to_string exp = exp |> E.to_string

  let to_simplified_string exp = exp |> simplify None |> to_string

  let print exp = exp |> to_string |> print_endline

  let print_simplified exp = exp |> simplify None |> to_string |> print_endline
end

module Tactic = struct
  type t = T.tactic

  let init name = T.mk_tactic ctx name

  let and_then tactic_names =
    let tactics = List.map init tactic_names in
    match tactics with
    | h :: s :: t -> T.and_then ctx h s t
    | _ -> failwith "require more than two tactics"
end

module Model = struct
  type t = M.model

  let to_str = M.to_string

  let eval t expr = M.eval t expr false |> Option.get
end

module Solver = struct
  type t = S.solver

  type status = SATISFIABLE | UNSATISFIABLE | UNKNOWN

  let init logic =
    match logic with
    | None -> S.mk_solver ctx None
    | Some logic -> S.mk_solver ctx (Some (Z3.Symbol.mk_string ctx logic))

  let init_with_tactic tactic = S.mk_solver_t ctx tactic

  let check solver query = S.check solver [ query ]

  let get_model = S.get_model

  let str_of_status = S.string_of_status
end

module Bool = struct
  type t = E.expr

  (* constructor *)
  let init name = B.mk_const_s ctx name

  let mk_sort = B.mk_sort ctx

  (* constants *)
  let tr = B.mk_true ctx

  let fl = B.mk_false ctx

  (* logical operation *)
  let and_ lexp rexp = B.mk_and ctx [ lexp; rexp ]

  let ands exps = B.mk_and ctx exps

  let or_ lexp rexp = B.mk_or ctx [ lexp; rexp ]

  let ors exps = B.mk_or ctx exps

  let not exp = B.mk_not ctx exp

  (* comparison *)
  let eq lexp rexp = B.mk_eq ctx lexp rexp

  let neq lexp rexp = B.mk_not ctx (B.mk_eq ctx lexp rexp)

  (* logic expression *)
  let implies cond t = B.mk_implies ctx cond t

  let ite cond t f = B.mk_ite ctx cond t f
end

module Float = struct
  type t = E.expr

  let rne_mode = Fl.RoundingMode.mk_rne ctx

  let rtn_mode = Fl.RoundingMode.mk_rtn ctx

  let rtp_mode = Fl.RoundingMode.mk_rtp ctx

  let rtz_mode = Fl.RoundingMode.mk_rtz ctx

  let single_sort = Fl.mk_sort_single ctx

  let double_sort = Fl.mk_sort_double ctx

  let minus_zero ?(sort = !float_sort) () = Fl.mk_numeral_s ctx "-0.0" sort

  let nan ?(sort = !float_sort) () = Fl.mk_nan ctx sort

  let inf ?(sort = !float_sort) () = Fl.mk_inf ctx sort false

  let ninf ?(sort = !float_sort) () = Fl.mk_inf ctx sort true

  let safe_integer_min ?(sort = !float_sort) () =
    Fl.mk_numeral_s ctx
      (Int64.of_string "-0x1fffffffffffff" |> Int64.to_string)
      sort

  let safe_integer_max ?(sort = !float_sort) () =
    Fl.mk_numeral_s ctx
      (Int64.of_string "0x1fffffffffffff" |> Int64.to_string)
      sort

  let from_float ?(sort = !float_sort) f = Fl.mk_numeral_f ctx f sort

  let from_string ?(sort = !float_sort) s =
    if String.equal s "nan" then nan ()
    else if String.equal s "inf" then inf ()
    else
      try Fl.mk_numeral_s ctx s sort
      with _ ->
        let reason = Format.sprintf "from_string: cannot parse %s" s in
        failwith reason

  let from_signed_bv ?(sort = !float_sort) bv =
    Fl.mk_to_fp_signed ctx rne_mode bv sort

  let from_unsigned_bv ?(sort = !float_sort) bv =
    Fl.mk_to_fp_unsigned ctx rne_mode bv sort

  let from_ieee_bv ?(sort = !float_sort) bv = Fl.mk_to_fp_bv ctx bv sort

  let to_sbv ?(len = !bvlen) rm t = Fl.mk_to_sbv ctx rm t len

  let to_ubv t = Fl.mk_to_ubv ctx t

  let to_ieee_bv t = Fl.mk_to_ieee_bv ctx t

  let to_real t = Fl.mk_to_real ctx t

  let round rm exp = Fl.mk_round_to_integral ctx rm exp

  let eq lexp rexp = Fl.mk_eq ctx lexp rexp

  let gt lexp rexp = Fl.mk_gt ctx lexp rexp

  let ge lexp rexp = Fl.mk_geq ctx lexp rexp

  let gef lexp rexp = Fl.mk_geq ctx lexp (rexp |> from_float)

  let lt lexp rexp = Fl.mk_lt ctx lexp rexp

  let le lexp rexp = Fl.mk_leq ctx lexp rexp

  let lef lexp rexp = Fl.mk_leq ctx lexp (rexp |> from_float)

  let add lexp rexp = Fl.mk_add ctx rne_mode lexp rexp

  let sub lexp rexp = Fl.mk_sub ctx rne_mode lexp rexp

  let div lexp rexp = Fl.mk_div ctx rne_mode lexp rexp

  let rem lexp rexp = Fl.mk_rem ctx lexp rexp

  let mul lexp rexp = Fl.mk_mul ctx rne_mode lexp rexp

  let abs exp = Fl.mk_abs ctx exp

  let neg exp = Fl.mk_neg ctx exp

  let is_negative exp = Fl.mk_is_negative ctx exp

  let is_positive exp = Fl.mk_is_positive ctx exp

  let is_zero exp = Fl.mk_is_zero ctx exp

  let is_minus_zero exp = Bool.ands [ is_negative exp; is_zero exp ]

  let is_nan exp = Fl.mk_is_nan ctx exp

  let is_inf exp = Fl.mk_is_infinite ctx exp

  let is_ninf exp = Bool.ands [ is_negative exp; is_inf exp ]
end

module BitVecVal = struct
  type t = E.expr

  (* numeral const *)
  let zero ?(len = !bvlen) () : t = BV.mk_numeral ctx "0" len

  let minus_zero ?(sort = !float_sort) () =
    Float.minus_zero ~sort () |> Float.to_ieee_bv

  let nan ?(sort = !float_sort) () = Float.nan ~sort () |> Float.to_ieee_bv

  let inf ?(sort = !float_sort) () = Float.inf ~sort () |> Float.to_ieee_bv

  let ninf ?(sort = !float_sort) () = Float.ninf ~sort () |> Float.to_ieee_bv

  (* constructor *)
  let from_int ?(len = !bvlen) value =
    BV.mk_numeral ctx (value |> string_of_int) len

  let from_istring ?(len = !bvlen) str =
    let dec_str =
      try Int64.of_string str |> Int64.to_string
      with Failure _ ->
        let c = str in
        let r =
          "%s has a invalid format or exceeds the range of integers \
           representable in type `int64`"
        in
        err (InvalidFormat (c, r))
    in

    BV.mk_numeral ctx dec_str len

  let from_f64string str =
    Float.from_string ~sort:Float.double_sort str |> Float.to_ieee_bv

  (* boolean const *)
  let tr ?(len = !bvlen) () = BV.mk_repeat ctx len (BV.mk_numeral ctx "1" 1)

  let fl ?(len = !bvlen) () = BV.mk_repeat ctx len (BV.mk_numeral ctx "0" 1)
end

module BitVec = struct
  type t = E.expr

  let init ?(len = !bvlen) name = BV.mk_const_s ctx name len

  let length_of bv = bv |> E.get_sort |> BV.get_size

  let mk_sort sz = BV.mk_sort ctx sz

  (* logical operation *)
  let andb lbv rbv = BV.mk_and ctx lbv rbv

  let andi lbv rval =
    let rbv = BitVecVal.from_int ~len:(length_of lbv) rval in
    BV.mk_and ctx lbv rbv

  let orb lbv rbv = BV.mk_or ctx lbv rbv

  let ori lbv rval =
    let rbv = BitVecVal.from_int ~len:(length_of lbv) rval in
    BV.mk_or ctx lbv rbv

  let notb bv = BV.mk_not ctx bv

  let shlb bv off = BV.mk_shl ctx bv off

  let shli bv off =
    let rbv = BitVecVal.from_int ~len:(length_of bv) off in
    BV.mk_shl ctx bv rbv

  let lshrb bv off = BV.mk_lshr ctx bv off

  let lshri bv off =
    let rbv = BitVecVal.from_int ~len:(length_of bv) off in
    BV.mk_lshr ctx bv rbv

  let xor lbv rbv = BV.mk_xor ctx lbv rbv

  let xori lbv rval =
    let rbv = BitVecVal.from_int ~len:(length_of lbv) rval in
    BV.mk_xor ctx lbv rbv

  (* comparison *)
  let eqb lbv rbv = B.mk_eq ctx lbv rbv

  let eqi lbv rval =
    let rbv = BitVecVal.from_int ~len:(length_of lbv) rval in
    B.mk_eq ctx lbv rbv

  let neqb lbv rbv = B.mk_not ctx (eqb lbv rbv)

  let neqi lbv rval = B.mk_not ctx (eqi lbv rval)

  let ugtb lbv rbv = BV.mk_ugt ctx lbv rbv

  let ugti lbv rval =
    BV.mk_ugt ctx lbv (BitVecVal.from_int ~len:(length_of lbv) rval)

  let sgeb lbv rbv = BV.mk_sge ctx lbv rbv

  let sgei lbv rval =
    BV.mk_sge ctx lbv (BitVecVal.from_int ~len:(length_of lbv) rval)

  let ugeb lbv rbv = BV.mk_uge ctx lbv rbv

  let ugei lbv rval =
    let rbv = BitVecVal.from_int ~len:(length_of lbv) rval in
    BV.mk_uge ctx lbv rbv

  let sltb lbv rbv = BV.mk_slt ctx lbv rbv

  let slti lbv rval =
    BV.mk_slt ctx lbv (BitVecVal.from_int ~len:(length_of lbv) rval)

  let sleb lbv rbv = BV.mk_sle ctx lbv rbv

  let slei lbv rval =
    BV.mk_sle ctx lbv (BitVecVal.from_int ~len:(length_of lbv) rval)

  let ultb lbv rbv = BV.mk_ult ctx lbv rbv

  let ulti lbv rval =
    let rbv = BitVecVal.from_int ~len:(length_of lbv) rval in
    BV.mk_ult ctx lbv rbv

  let uleb lbv rbv = BV.mk_ule ctx lbv rbv

  let ulei lbv rval =
    let rbv = BitVecVal.from_int ~len:(length_of lbv) rval in
    BV.mk_ule ctx lbv rbv

  let gef lbv rval =
    let lval = Float.from_ieee_bv lbv in
    Float.gef lval rval

  let lef lbv rval =
    let lval = Float.from_ieee_bv lbv in
    Float.lef lval rval

  (* arithmetic operation *)
  let addb lbv rbv = BV.mk_add ctx lbv rbv

  let add_no_overflow lbv rbv sign = BV.mk_add_no_overflow ctx lbv rbv sign

  let add_no_underflow lbv rbv = BV.mk_add_no_underflow ctx lbv rbv

  let addi lbv rval =
    let rbv = BitVecVal.from_int ~len:(length_of lbv) rval in
    BV.mk_add ctx lbv rbv

  let sdivb lbv rbv = BV.mk_sdiv ctx lbv rbv

  let udivb lbv rbv = BV.mk_udiv ctx lbv rbv

  let subb lbv rbv = BV.mk_sub ctx lbv rbv

  let sub_no_overflow lbv rbv = BV.mk_sub_no_overflow ctx lbv rbv

  let sub_no_underflow lbv rbv sign = BV.mk_sub_no_underflow ctx lbv rbv sign

  let subi lbv rval =
    BV.mk_sub ctx lbv (BitVecVal.from_int ~len:(length_of lbv) rval)

  let abs bv = Bool.ite (slti bv 0) (BV.mk_neg ctx bv) bv

  (* rbv != 0 && lbv % rbv *)
  let modb lbv rbv = BV.mk_smod ctx lbv rbv

  let modi lbv rval =
    if rval = 0 then failwith "modi: division by zero"
    else
      let rbv = BitVecVal.from_int ~len:(length_of lbv) rval in
      modb lbv rbv

  let mulb lbv rbv = BV.mk_mul ctx lbv rbv

  let muli lbv rval =
    let rbv = BitVecVal.from_int ~len:(length_of lbv) rval in
    BV.mk_mul ctx lbv rbv

  let mul_no_overflow lbv rbv sign = BV.mk_mul_no_overflow ctx lbv rbv sign

  let mul_no_underflow lbv rbv = BV.mk_mul_no_underflow ctx lbv rbv

  let neg bv = BV.mk_neg ctx bv

  let ashrb lbv rbv = BV.mk_ashr ctx lbv rbv

  let ashri lbv rval =
    let rbv = BitVecVal.from_int ~len:(length_of lbv) rval in
    BV.mk_ashr ctx lbv rbv

  (* boolean operation *)
  let is_true bv =
    let fbv = BitVecVal.fl ~len:(length_of bv) () in
    neqb bv fbv

  let is_false bv =
    let fbv = BitVecVal.fl ~len:(length_of bv) () in
    eqb bv fbv

  (* Un-BitVec Operation*)
  let extract high low bv = BV.mk_extract ctx high low bv

  let repeat cnt bv = BV.mk_repeat ctx cnt bv

  let sign_extend len bv = BV.mk_sign_ext ctx len bv

  let zero_extend len bv = BV.mk_zero_ext ctx len bv

  (* ((x << 24) & 0xff000000) |
   * ((x <<  8) & 0x00ff0000) |
   * ((x >>  8) & 0x0000ff00) |
   * ((x >> 24) & 0x000000ff) *)
  let swap32 bv =
    let len = 32 in
    let mask1 = BitVecVal.from_int ~len 0xff000000 in
    let mask2 = BitVecVal.from_int ~len 0x00ff0000 in
    let mask3 = BitVecVal.from_int ~len 0x0000ff00 in
    let mask4 = BitVecVal.from_int ~len 0x000000ff in
    let b1 = andb (shli bv 24) mask1 in
    let b2 = andb (shli bv 8) mask2 in
    let b3 = andb (lshri bv 8) mask3 in
    let b4 = andb (lshri bv 24) mask4 in
    orb b1 b2 |> orb b3 |> orb b4

  (* ((x << 56) & 0xff00000000000000) |
   * ((x << 40) & 0x00ff000000000000) |
   * ((x << 24) & 0x0000ff0000000000) |
   * ((x <<  8) & 0x000000ff00000000) |
   * ((x >>  8) & 0x00000000ff000000) |
   * ((x >> 24) & 0x0000000000ff0000) |
   * ((x >> 40) & 0x000000000000ff00) |
   * ((x >> 56) & 0x00000000000000ff) *)
  let swap64 bv =
    let len = 64 in
    let mask1 = BitVecVal.from_istring ~len "0xff00000000000000" in
    let mask2 = BitVecVal.from_int ~len 0x00ff000000000000 in
    let mask3 = BitVecVal.from_int ~len 0x0000ff0000000000 in
    let mask4 = BitVecVal.from_int ~len 0x000000ff00000000 in
    let mask5 = BitVecVal.from_int ~len 0x00000000ff000000 in
    let mask6 = BitVecVal.from_int ~len 0x0000000000ff0000 in
    let mask7 = BitVecVal.from_int ~len 0x000000000000ff00 in
    let mask8 = BitVecVal.from_int ~len 0x00000000000000ff in
    let b1 = andb (shli bv 56) mask1 in
    let b2 = andb (shli bv 40) mask2 in
    let b3 = andb (shli bv 24) mask3 in
    let b4 = andb (shli bv 8) mask4 in
    let b5 = andb (lshri bv 8) mask5 in
    let b6 = andb (lshri bv 24) mask6 in
    let b7 = andb (lshri bv 40) mask7 in
    let b8 = andb (lshri bv 56) mask8 in
    orb b1 b2 |> orb b3 |> orb b4 |> orb b5 |> orb b6 |> orb b7 |> orb b8

  (* Bi-BitVec operation *)
  let concat lbv rbv = BV.mk_concat ctx lbv rbv

  let to_sint bv = BV.mk_bv2int ctx bv true

  let to_uint bv = BV.mk_bv2int ctx bv false
end

module Array = struct
  type t = E.expr

  let init name domain range = A.mk_const_s ctx name domain range

  let store value key arr = A.mk_store ctx arr key value

  let select key arr = A.mk_select ctx arr key
end

module Integer = struct
  type t = E.expr

  let from_int i = I.mk_numeral_i ctx i

  let ge lexp rexp = AR.mk_ge ctx lexp rexp

  let sub lexp rexp = AR.mk_sub ctx [ lexp; rexp ]

  let mod_ lexp rexp = I.mk_mod ctx lexp rexp

  let to_bv ?(len = !bvlen) exp = I.mk_int2bv ctx len exp
end

module Real = struct
  type t = E.expr

  let to_decimal_string t = R.to_decimal_string t 5

  let to_integer t = R.mk_real2int ctx t
end

let sort_equal e1 e2 = Z3.Sort.equal (Z3.Expr.get_sort e1) (Z3.Expr.get_sort e2)
