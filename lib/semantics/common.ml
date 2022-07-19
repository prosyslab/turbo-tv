open Z3utils
module Composed = Value.Composed
module ControlTuple = Control.ControlTuple
module HeapNumber = Objects.HeapNumber

(* common: constants *)
(* assertion: value = c *)
let float64_constant c state =
  let value = c |> Value.cast Type.float64 in
  state |> State.update ~value

(* assertion: value = c *)
let int32_constant c state =
  let value = c |> Value.cast Type.int32 in
  state |> State.update ~value

(* behavior: value=c *)
let int64_constant c state =
  let value = c |> Value.cast Type.int64 in
  state |> State.update ~value

(* behavior: value=c *)
let external_constant c state =
  let value = c |> Value.cast Type.pointer in
  state |> State.update ~value

(* behavior: value=c *)
let number_constant c mem state =
  let next_bid = ref (State.next_bid state) in
  let ptr = HeapNumber.allocate next_bid in
  HeapNumber.store ptr (HeapNumber.from_number_string c) Bool.tr mem;
  let value = ptr in
  state |> State.update ~value

(* common: control *)
(* retrieve the value at [idx] from [incoming]
 * incoming: | --- idx[0] ---| --- idx[1] --- | --- ... --- |
 * well-defined condition:
 * - 0 <= idx <= 2 ^ idx <= ||incoming||
 * assertion:
 *  value = ite well-defined value=incoming[idx] value=UB *)
let projection idx incoming state =
  (* currently, idx of projection is assumebed to be less than 2 *)
  let value = incoming |> Composed.select idx in
  let ub =
    if not (0 <= idx && idx < 2 && idx <= Composed.size_of incoming) then
      Bool.tr
    else Bool.fl
  in
  state |> State.update ~value ~ub

(* well-defined condition:
 * - Bool(cond) ^ Bool(precond)
 * - WellDefined(cond) ^ WellDefined(precond)
 * assertion:
 *  ct = ite well-defined (precond ^ cond, precond ^ not cond) (UB, UB) *)
let branch cond precond state =
  let for_true = Bool.and_ precond (Value.is_true cond) in
  let for_false = Bool.and_ precond (Value.is_false cond) in
  let control = ControlTuple.from_tf for_true for_false in
  state |> State.update ~control

(* well-defined condition:
 * - Bool(FalseCond(cond))
 * - WellDefined(FalseCond(cond))
 * assertion:
 *  ct = ite well-defined FalseCond(Cond) UB *)
let if_false cond state =
  let control = cond |> ControlTuple.false_cond in
  state |> State.update ~control

(* well-defined condition:
 *  - Bool(TrueCond(cond))
 *  - WellDefined(TrueCond(cond))
 * assertion:
 *  value = ite well-defined TrueCond(Cond) UB *)
let if_true cond state =
  let control = cond |> ControlTuple.true_cond in
  state |> State.update ~control

(* merge every incoming execution condition *)
let merge conds state =
  (* cond could be composed value *)
  let control = Bool.ors conds in
  state |> State.update ~control

let phi incomings repr ctrls state =
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

  let value = wd_value in
  state |> State.update ~value

let select cond tr fl state =
  let ub = Bool.not (cond |> Value.has_type Type.bool) in
  let value = Bool.ite (Value.is_true cond) tr fl in
  state |> State.update ~value ~ub

let throw control state = state |> State.update ~control

(* common: deoptimization *)
let deoptimize _frame _mem control state =
  state |> State.update ~control ~deopt:Bool.tr

let deoptimize_unless cond _frame _mem control state =
  let deopt = Bool.ite (Value.is_false cond) Bool.tr Bool.fl in
  state |> State.update ~control ~deopt

(* common: procedure *)
let parameter param state =
  (* assume parameter is tagged signed or heap number
     [TODO] allow parameter to point random address after implement the other object types
  *)
  (* let assertion =
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
     in *)
  let value = param in
  state |> State.update ~value

let return return_value state =
  let value = return_value in
  state |> State.update ~value

let start state = state |> State.update ~control:Bool.tr
