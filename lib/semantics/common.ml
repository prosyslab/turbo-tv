open Z3utils
module Composed = Value.Composed
module ControlTuple = Control.ControlTuple
module HeapNumber = Objects.HeapNumber

(* common: constants *)
(* assertion: value = c *)
let float64_constant vid c =
  let value = Value.init vid in
  let assertion = Value.eq value c in
  (value, Control.empty, assertion, Bool.fl)

(* well-defined condition: INT32_MIN <= c <= INT32_MAX
 * behavior: ite well-defined value=c value=UB *)
let int32_constant vid c =
  let value = Value.init vid in
  let wd_cond =
    Bool.ands [ Value.sge c Value.int32_min; Value.sle c Value.int32_max ]
  in
  let assertion =
    Value.eq value
      (Bool.ite wd_cond (c |> Value.cast Type.int32) Value.undefined)
  in
  (value, Control.empty, assertion, Bool.fl)

(* behavior: value=c *)
let int64_constant vid c =
  let value = Value.init vid in
  let assertion = Value.eq value (c |> Value.cast Type.int64) in
  (value, Control.empty, assertion, Bool.fl)

(* behavior: value=c *)
let external_constant vid c =
  let value = Value.init vid in
  let assertion = Value.eq value (c |> Value.cast Type.pointer) in
  (value, Control.empty, assertion, Bool.fl)

(* behavior: value=c *)
let heap_constant = external_constant

(* behavior: value=c *)
let number_constant vid c mem =
  let value = Value.init vid in
  let wd_value = HeapNumber.allocate in
  HeapNumber.store wd_value (HeapNumber.from_number_string c) Bool.tr mem;
  let assertion = Value.eq value wd_value in
  (value, Control.empty, assertion, Bool.fl)

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
  let assertion =
    Value.eq value (if wd_cond then wd_value else Value.undefined)
  in
  (value, Control.empty, assertion, Bool.fl)

(* well-defined condition:
 * - Bool(cond) ^ Bool(precond)
 * - WellDefined(cond) ^ WellDefined(precond)
 * assertion:
 *  ct = ite well-defined (precond ^ cond, precond ^ not cond) (UB, UB) *)
let branch cid cond precond =
  let control = ControlTuple.init cid in
  let wd_cond = Bool.ands [ Value.is_defined cond ] in
  let for_true = Bool.and_ precond (Value.is_true cond) in
  let for_false = Bool.and_ precond (Value.is_false cond) in
  let wd_value = ControlTuple.from_tf for_true for_false in
  let ud_value = ControlTuple.from_tf Bool.fl Bool.fl in
  let assertion =
    ControlTuple.eq control (Bool.ite wd_cond wd_value ud_value)
  in
  (Value.empty, control, assertion, Bool.fl)

(* well-defined condition:
 * - Bool(FalseCond(cond))
 * - WellDefined(FalseCond(cond))
 * assertion:
 *  ct = ite well-defined FalseCond(Cond) UB *)
let if_false cid cond =
  let control = Control.init cid in
  let false_cond = cond |> ControlTuple.false_cond in
  let assertion = Bool.eq control false_cond in
  (Value.empty, control, assertion, Bool.fl)

(* well-defined condition:
 *  - Bool(TrueCond(cond))
 *  - WellDefined(TrueCond(cond))
 * assertion:
 *  value = ite well-defined TrueCond(Cond) UB *)
let if_true cid cond =
  let control = Control.init cid in
  let true_cond = cond |> ControlTuple.true_cond in
  let assertion = Bool.eq control true_cond in
  (Value.empty, control, assertion, Bool.fl)

(* merge every incoming execution condition *)
let merge cid conds =
  (* cond could be composed value *)
  let control = Control.init cid in
  let merged = Bool.ors conds in
  let assertion = Value.eq control merged in
  (Value.empty, control, assertion, Bool.fl)

let phi vid incoming repr conds =
  let value = Value.init vid in
  (* select one of types candidated by repr *)
  let ty = Type.from_repr repr |> List.hd in
  let rec mk_value values conds =
    match values with
    | h :: [ t ] ->
        Bool.ite (List.hd conds) (h |> Value.cast ty) (t |> Value.cast ty)
    | h :: t when List.length t > 1 ->
        Bool.ite (List.hd conds)
          (h |> Value.cast ty)
          (mk_value t (List.tl conds))
    (* length of incoming is larger than 1 *)
    | [ _ ] -> failwith "unreachable"
    | _ -> failwith "unreachable"
  in
  let wd_value = mk_value incoming conds in
  let assertion = Value.eq value wd_value in
  (value, Control.empty, assertion, Bool.fl)

(* common: procedure *)
let parameter vid param =
  let value = Value.init vid in
  let assertion =
    Value.eq value
      (Value.andi param Constants.smi_mask |> Value.cast Type.tagged_signed)
  in
  (value, Control.empty, assertion, Bool.fl)

let return vid return_value =
  let value = Value.init vid in
  let assertion = Value.eq value return_value in
  (value, Control.empty, assertion, Bool.fl)

let start cid =
  let control = Control.init cid in
  let assertion = Bool.eq control Bool.tr in
  (Value.empty, control, assertion, Bool.fl)
