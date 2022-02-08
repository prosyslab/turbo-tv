open Err
module B = Z3.Boolean
module E = Z3.Expr
module S = Z3.Solver
module BV = Z3.BitVector

(* global context *)
let ctx = Z3.mk_context [ ("model", "true"); ("unsat_core", "true") ]

(* print *)
let str_of_exp exp = exp |> E.to_string
let simplify opt exp = E.simplify exp opt
let print exp = exp |> str_of_exp |> print_endline
let print_simplified exp = exp |> simplify None |> str_of_exp |> print_endline

(* default bitvector length *)
let bvlen = ref 64
let set_bvlen len = bvlen := len

module Solver = struct
  type t = S.solver

  let init = S.mk_solver ctx None
  let check solver query = S.check solver [ query ]
  let str_of_status = S.string_of_status
end

module Bool = struct
  type t = E.expr

  (* constructor *)
  let init name = B.mk_const_s ctx name

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
end

module BitVecVal = struct
  type t = E.expr

  (* numeral const *)
  let zero (len : int) () : t = BV.mk_numeral ctx "0" len

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
  let tr ?(len = !bvlen) () = BV.mk_numeral ctx "1" len
  let fl ?(len = !bvlen) () = BV.mk_numeral ctx "0" len
end

module BitVec = struct
  type t = E.expr

  let init ?(len = !bvlen) name = BV.mk_const_s ctx name len
  let len bv = bv |> E.get_sort |> BV.get_size

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

  (* comparison *)
  let eqb lbv rbv = B.mk_eq ctx lbv rbv

  let eqi lbv rval =
    let rbv = BitVecVal.of_int ~len:(len lbv) rval in
    B.mk_eq ctx lbv rbv

  let neqb lbv rbv = B.mk_not ctx (eqb lbv rbv)
  let neqi lbv rval = B.mk_not ctx (eqi lbv rval)
  let ugeb lbv rbv = BV.mk_uge ctx lbv rbv

  let ugei lbv rval =
    let rbv = BitVecVal.of_int ~len:(len lbv) rval in
    BV.mk_uge ctx lbv rbv

  (* arithmetic operation *)
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
end
