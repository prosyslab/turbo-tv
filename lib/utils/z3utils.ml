open Err
module A = Z3.Z3Array
module B = Z3.Boolean
module E = Z3.Expr
module M = Z3.Model
module S = Z3.Solver
module BV = Z3.BitVector
module Fl = Z3.FloatingPoint

(* global context *)
let ctx = Z3.mk_context [ ("model", "true"); ("unsat_core", "true") ]

(* print *)
let simplify opt exp = E.simplify exp opt

let str_of_exp exp = exp |> E.to_string

let str_of_simplified exp = exp |> simplify None |> str_of_exp

let print_exp exp = exp |> str_of_exp |> print_endline

let print_simplified exp = exp |> simplify None |> str_of_exp |> print_endline

(* default bitvector length *)
let bvlen = ref 64

let set_bvlen len = bvlen := len

module Model = struct
  type t = M.model

  let to_str = M.to_string
end

module Solver = struct
  type t = S.solver

  type status = SATISFIABLE | UNSATISFIABLE | UNKNOWN

  let init = S.mk_solver ctx None

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

module BitVecVal = struct
  type t = E.expr

  (* numeral const *)
  let zero ?(len = !bvlen) () : t = BV.mk_numeral ctx "0" len

  (* constructor *)
  let of_int ?(len = !bvlen) value =
    BV.mk_numeral ctx (value |> string_of_int) len

  let of_str ?(len = !bvlen) str =
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

  (* boolean const *)
  let tr ?(len = !bvlen) () = BV.mk_repeat ctx len (BV.mk_numeral ctx "1" 1)

  let fl ?(len = !bvlen) () = BV.mk_repeat ctx len (BV.mk_numeral ctx "0" 1)
end

module BitVec = struct
  type t = E.expr

  let init ?(len = !bvlen) name = BV.mk_const_s ctx name len

  let len bv = bv |> E.get_sort |> BV.get_size

  let mk_sort sz = BV.mk_sort ctx sz

  (* logical operation *)
  let andb lbv rbv = BV.mk_and ctx lbv rbv

  let andi lbv rval =
    let rbv = BitVecVal.of_int ~len:(len lbv) rval in
    BV.mk_and ctx lbv rbv

  let orb lbv rbv = BV.mk_or ctx lbv rbv

  let ori lbv rval =
    let rbv = BitVecVal.of_int ~len:(len lbv) rval in
    BV.mk_or ctx lbv rbv

  let notb bv = BV.mk_not ctx bv

  let shlb bv off = BV.mk_shl ctx bv off

  let shli bv off =
    let rbv = BitVecVal.of_int ~len:(len bv) off in
    BV.mk_shl ctx bv rbv

  let lshrb bv off = BV.mk_lshr ctx bv off

  let lshri bv off =
    let rbv = BitVecVal.of_int ~len:(len bv) off in
    BV.mk_lshr ctx bv rbv

  let xori lbv rval =
    let rbv = BitVecVal.of_int ~len:(len lbv) rval in
    BV.mk_xor ctx lbv rbv

  (* comparison *)
  let eqb lbv rbv = B.mk_eq ctx lbv rbv

  let eqi lbv rval =
    let rbv = BitVecVal.of_int ~len:(len lbv) rval in
    B.mk_eq ctx lbv rbv

  let neqb lbv rbv = B.mk_not ctx (eqb lbv rbv)

  let neqi lbv rval = B.mk_not ctx (eqi lbv rval)

  let sgeb lbv rbv = BV.mk_sge ctx lbv rbv

  let sgei lbv rval = BV.mk_sge ctx lbv (BitVecVal.of_int ~len:(len lbv) rval)

  let ugeb lbv rbv = BV.mk_uge ctx lbv rbv

  let ugei lbv rval =
    let rbv = BitVecVal.of_int ~len:(len lbv) rval in
    BV.mk_uge ctx lbv rbv

  let sltb lbv rbv = BV.mk_slt ctx lbv rbv

  let slti lbv rval = BV.mk_slt ctx lbv (BitVecVal.of_int ~len:(len lbv) rval)

  let slei lbv rval = BV.mk_sle ctx lbv (BitVecVal.of_int ~len:(len lbv) rval)

  let ultb lbv rbv = BV.mk_ult ctx lbv rbv

  let ulti lbv rval =
    let rbv = BitVecVal.of_int ~len:(len lbv) rval in
    BV.mk_ult ctx lbv rbv

  let uleb lbv rbv = BV.mk_ule ctx lbv rbv

  let ulei lbv rval =
    let rbv = BitVecVal.of_int ~len:(len lbv) rval in
    BV.mk_ule ctx lbv rbv

  (* arithmetic operation *)
  let addb lbv rbv = BV.mk_add ctx lbv rbv

  let addi lbv rval =
    let rbv = BitVecVal.of_int ~len:(len lbv) rval in
    BV.mk_add ctx lbv rbv

  let subb lbv rbv = BV.mk_sub ctx lbv rbv

  let subi lbv rval = BV.mk_sub ctx lbv (BitVecVal.of_int ~len:(len lbv) rval)

  (* rbv != 0 && lbv % rbv *)
  let modb lbv rbv =
    let zdiv_cond = neqi rbv 0 in
    andb zdiv_cond (BV.mk_smod ctx lbv rbv)

  let ashrb lbv rbv = BV.mk_ashr ctx lbv rbv

  let ashri lbv rval =
    let rbv = BitVecVal.of_int ~len:(len lbv) rval in
    BV.mk_ashr ctx lbv rbv

  (* boolean operation *)
  let is_true bv =
    let fbv = BitVecVal.fl ~len:(len bv) () in
    neqb bv fbv

  let is_false bv =
    let fbv = BitVecVal.fl ~len:(len bv) () in
    eqb bv fbv

  (* Un-BitVec Operation*)
  let extract high low bv = BV.mk_extract ctx high low bv

  let repeat cnt bv = BV.mk_repeat ctx cnt bv

  let zero_extend len bv = BV.mk_zero_ext ctx len bv

  (* Bi-BitVec operation *)
  let concat lbv rbv = BV.mk_concat ctx lbv rbv
end

module Array = struct
  type t = E.expr

  let init name domain range = A.mk_const_s ctx name domain range

  let store value key arr = A.mk_store ctx arr key value

  let select key arr = A.mk_select ctx arr key
end

module Float = struct
  type t = E.expr

  let double_sort = Fl.mk_sort_double ctx

  let minus_zero sort = Fl.mk_numeral_s ctx "-0" sort

  let of_str s sort = Fl.mk_numeral_s ctx s sort

  let to_ieee_bv t = Fl.mk_to_ieee_bv ctx t
end