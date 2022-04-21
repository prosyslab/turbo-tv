open Z3utils
module Composed = Value.Composed

(* common: constants *)
(* well-defined condition: INT32_MIN <= [c] <= INT32_MAX
 * behavior: ite well-defined value=c value=UB *)
let int32_constant vid c =
  let value = Value.init vid in
  let c_can_be_int32 =
    Bool.ands [ Value.sge c Value.int32_min; Value.sle c Value.int32_max ]
  in
  let wd_cond = c_can_be_int32 in
  let assertion = Value.eq value (Bool.ite wd_cond c Value.undefined) in
  (value, assertion)

(* well-defined condition: INT64_MIN <= c <= INT64_MAX
 * behavior: ite well-defined value=c value=UB *)
let int64_constant vid c =
  let value = Value.init vid in
  let c_can_be_int64 =
    Bool.ands [ Value.sge c Value.int64_min; Value.sle c Value.int64_max ]
  in
  let wd_cond = c_can_be_int64 in
  let assertion = Value.eq value (Bool.ite wd_cond c Value.undefined) in
  (value, assertion)

(* well-defined condition: UINT64_MIN <= c <= UINT64_MAX
 * behavior: ite well-defined value=c value=UB *)
let external_constant vid c =
  let value = Value.init vid in
  let c_can_be_pointer =
    Bool.ands [ Value.uge c Value.uint64_min; Value.ule c Value.uint64_max ]
  in
  let wd_cond = c_can_be_pointer in
  let assertion = Value.eq value (Bool.ite wd_cond c Value.undefined) in
  (value, assertion)

let heap_constant = external_constant

(* well-defined condition: true
 * behavior: value=c *)

let number_constant vid c =
  let value = Value.init vid in
  let assertion = Value.eq value c in
  (value, assertion)

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
  (value, assertion)

(* well-defined condition:
 * - Bool(cond) ^ Bool(precond)
 * - WellDefined(cond) ^ WellDefined(precond)
 * assertion:
 *  value = ite well-defined (precond ^ cond :: precond ^ not cond) (UB::UB) *)
let branch vid cond precond =
  let value = Composed.init vid 2 in
  let wd_cond =
    let conds_are_bool =
      Bool.ands
        [ Value.has_type Type.bool cond; Value.has_type Type.bool precond ]
    in
    let conds_are_defined =
      Bool.ands [ Value.is_defined cond; Value.is_defined precond ]
    in
    Bool.ands [ conds_are_bool; conds_are_defined ]
  in
  let wd_value =
    let tr_v = Value.and_ precond cond in
    let fl_v = Value.and_ precond (Value.not_ cond) in
    Composed.from_values [ tr_v; fl_v ]
  in
  let ud_value = Composed.from_values [ Value.undefined; Value.undefined ] in
  let assertion = Value.eq value (Bool.ite wd_cond wd_value ud_value) in
  (value, assertion)

(* well-defined condition:
 * - Bool(FalseCond(cond))
 * - WellDefined(FalseCond(cond))
 * assertion:
 *  value = ite well-defined FalseCond(Cond) UB *)
let if_false vid cond =
  let value = Value.init vid in
  let false_cond = cond |> Composed.second_of in
  let wd_cond =
    let cond_is_defined = Value.is_defined false_cond in
    let cond_is_bool = false_cond |> Value.has_type Type.bool in
    Bool.ands [ cond_is_bool; cond_is_defined ]
  in
  let assertion =
    Value.eq value (Bool.ite wd_cond false_cond Value.undefined)
  in
  (value, assertion)

(* well-defined condition:
 *  - Bool(TrueCond(cond))
 *  - WellDefined(TrueCond(cond))
 * assertion:
 *  value = ite well-defined TrueCond(Cond) UB *)
let if_true vid cond =
  let value = Value.init vid in
  let true_cond = cond |> Composed.first_of in
  let wd_cond =
    let is_cond_defined = Value.is_defined true_cond in
    let is_cond_bool = cond |> Value.has_type Type.bool in
    Bool.ands [ is_cond_bool; is_cond_defined ]
  in
  let assertion = Value.eq value (Bool.ite wd_cond true_cond Value.undefined) in
  (value, assertion)

(* merge every incoming execution condition *)
let merge vid conds =
  (* cond could be composed value *)
  let value =
    Composed.init vid
      (List.fold_left (fun res cond -> res + Composed.size_of cond) 0 conds)
  in
  let rec concat_conds res conds =
    match conds with
    | [] -> res
    | cond :: rest -> concat_conds (BitVec.concat res cond) rest
  in
  let assertion =
    Value.eq value (concat_conds (List.hd conds) (List.tl conds))
  in
  (value, assertion)

(* common: procedure *)
let parameter vid param =
  let value = Value.init vid in
  let assertion = Value.eq value (param |> Value.cast Type.tagged_signed) in
  (value, assertion)

let return vid return_value =
  let value = Value.init vid in
  let assertion = Value.eq value return_value in
  (value, assertion)
