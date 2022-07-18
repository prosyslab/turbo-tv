open Z3utils
module Composed = Value.Composed
module ControlTuple = Control.ControlTuple
module HeapNumber = Objects.HeapNumber

(* common: constants *)
(* assertion: value = c *)
let float64_constant vid c =
  let value = Value.init vid in
  let assertion = Value.eq value (c |> Value.cast Type.float64) in
  (value, Control.empty, assertion, Bool.fl, Bool.fl)

(* assertion: value = c *)
let int32_constant vid c =
  let value = Value.init vid in
  let assertion = Value.eq value (c |> Value.cast Type.int32) in
  (value, Control.empty, assertion, Bool.fl, Bool.fl)

(* behavior: value=c *)
let int64_constant vid c =
  let value = Value.init vid in
  let assertion = Value.eq value (c |> Value.cast Type.int64) in
  (value, Control.empty, assertion, Bool.fl, Bool.fl)

(* behavior: value=c *)
let external_constant vid c =
  let value = Value.init vid in
  let assertion = Value.eq value (c |> Value.cast Type.pointer) in
  (value, Control.empty, assertion, Bool.fl, Bool.fl)

(* behavior: value=c *)
let number_constant vid c next_bid mem =
  let value = Value.init vid in
  let wd_value = HeapNumber.allocate next_bid in
  HeapNumber.store wd_value (HeapNumber.from_number_string c) Bool.tr mem;
  let assertion = Value.eq value wd_value in
  (value, Control.empty, assertion, Bool.fl, Bool.fl)

(* common: control *)
(* retrieve the value at [idx] from [incoming]
 * incoming: | --- idx[0] ---| --- idx[1] --- | --- ... --- |
 * well-defined condition:
 * - 0 <= idx <= 2 ^ idx <= ||incoming||
 * assertion:
 *  value = ite well-defined value=incoming[idx] value=UB *)
let projection vid idx incoming =
  (* currently, idx of projection is assumebed to be less than 2 *)
  let value = Value.init vid in
  let wd_cond = 0 <= idx && idx < 2 && idx <= Composed.size_of incoming in
  let wd_value = incoming |> Composed.select idx in
  let assertion = Value.eq value wd_value in
  ( value,
    Control.empty,
    assertion,
    (if wd_cond then Bool.fl else Bool.tr),
    Bool.fl )

(* well-defined condition:
 * - Bool(cond) ^ Bool(precond)
 * - WellDefined(cond) ^ WellDefined(precond)
 * assertion:
 *  ct = ite well-defined (precond ^ cond, precond ^ not cond) (UB, UB) *)
let branch cid cond precond =
  let control = ControlTuple.init cid in
  let for_true = Bool.and_ precond (Value.is_true cond) in
  let for_false = Bool.and_ precond (Value.is_false cond) in
  let wd_value = ControlTuple.from_tf for_true for_false in
  let assertion = ControlTuple.eq control wd_value in
  (Value.empty, control, assertion, Bool.fl, Bool.fl)

(* well-defined condition:
 * - Bool(FalseCond(cond))
 * - WellDefined(FalseCond(cond))
 * assertion:
 *  ct = ite well-defined FalseCond(Cond) UB *)
let if_false cid cond =
  let control = Control.init cid in
  let false_cond = cond |> ControlTuple.false_cond in
  let assertion = Bool.eq control false_cond in
  (Value.empty, control, assertion, Bool.fl, Bool.fl)

(* well-defined condition:
 *  - Bool(TrueCond(cond))
 *  - WellDefined(TrueCond(cond))
 * assertion:
 *  value = ite well-defined TrueCond(Cond) UB *)
let if_true cid cond =
  let control = Control.init cid in
  let true_cond = cond |> ControlTuple.true_cond in
  let assertion = Bool.eq control true_cond in
  (Value.empty, control, assertion, Bool.fl, Bool.fl)

(* merge every incoming execution condition *)
let merge cid conds =
  (* cond could be composed value *)
  let control = Control.init cid in
  let merged = Bool.ors conds in
  let assertion = Value.eq control merged in
  (Value.empty, control, assertion, Bool.fl, Bool.fl)

let phi vid incomings repr ctrls =
  let value = Value.init vid in
  (* select one of types candidated by repr *)
  let ty = Type.from_repr repr |> List.hd in
  let rec mk_value values conds =
    match values with
    | h :: [ t ] -> Bool.ite (List.hd conds) h t
    | h :: t when List.length t > 1 ->
        Bool.ite (List.hd conds) h (mk_value t (List.tl conds))
    (* length of incoming is larger than 1 *)
    | [ _ ] -> failwith "unreachable"
    | _ -> failwith "unreachable"
  in

  (* settle [incoming_value] to the 'tagged signed' type or 'tagged pointer type' if [ty] is 'any tagged' *)
  let wd_value =
    let incoming_value = mk_value incomings ctrls in
    if ty = Type.any_tagged then Value.AnyTagged.settle incoming_value
    else incoming_value |> Value.cast ty
  in

  let assertion = Value.eq value wd_value in
  (value, Control.empty, assertion, Bool.fl, Bool.fl)

let select vid cond tr fl =
  let value = Value.init vid in
  let wd_cond = cond |> Value.has_type Type.bool in
  let res = Bool.ite (Value.is_true cond) tr fl in
  let assertion = Value.eq value res in
  (value, Control.empty, assertion, Bool.not wd_cond, Bool.fl)

let throw cid cond =
  let control = Control.init cid in
  let assertion = Value.eq control cond in
  (Value.empty, control, assertion, Bool.fl, Bool.fl)

(* common: deoptimization *)
let deoptimize_unless cond _frame _mem control =
  let deopt_cond = Bool.ite (Value.is_false cond) Bool.tr Bool.fl in
  (Value.empty, control, Bool.tr, Bool.fl, deopt_cond)

(* common: procedure *)
let parameter vid param mem =
  let value = Value.init vid in
  (* assume parameter is tagged signed or heap number
     [TODO] allow parameter to point random address after implement the other object types
  *)
  let assertion =
    Bool.ands
      [
        Value.eq value param;
        Bool.ors
          [
            Value.has_type Type.tagged_signed param;
            Bool.ands
              [
                Value.has_type Type.tagged_pointer param;
                Objects.is_heap_number param mem;
              ];
          ];
      ]
  in
  (value, Control.empty, assertion, Bool.fl, Bool.fl)

let return vid return_value =
  let value = Value.init vid in
  let assertion = Value.eq value return_value in
  (value, Control.empty, assertion, Bool.fl, Bool.fl)

let start cid =
  let control = Control.init cid in
  let assertion = Bool.eq control Bool.tr in
  (Value.empty, control, assertion, Bool.fl, Bool.fl)
