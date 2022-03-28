open Z3utils
module Composed = Value.Composed

(* common: constants *)
let int32_constant vid c =
  let value = Value.init vid in
  let cval = c |> Value.from_string |> Value.cast Type.int32 in
  let assertion =
    Bool.ands
      [
        BitVec.sgei cval (Int32.min_int |> Int32.to_int);
        BitVec.slei cval (Int32.max_int |> Int32.to_int);
        Value.is_equal value cval;
      ]
  in
  (value, assertion)

let int64_constant vid c =
  let value = Value.init vid in
  let cval = c |> Value.from_string |> Value.cast Type.int64 in
  let assertion =
    Bool.ands
      [
        BitVec.sgei cval (Int64.min_int |> Int64.to_int);
        BitVec.slei cval (Int64.max_int |> Int64.to_int);
        Value.is_equal value cval;
      ]
  in
  (value, assertion)

let external_constant vid c =
  let value = Value.init vid in
  let cval = c |> Value.from_string |> Value.cast Type.pointer in
  let assertion = Bool.ands [ Value.is_equal value cval ] in
  (value, assertion)

let heap_constant = external_constant

let number_constant vid n =
  let value = Value.init vid in
  let cval = Value.from_string n in

  let can_be_smi = Value.can_be_smi cval in
  let tr =
    (* shift-left once  *)
    let smi_value = Value.shli value 1 |> Value.cast Type.tagged_signed in
    Value.is_equal value smi_value
  in
  let fl = Value.is_equal value (cval |> Value.cast Type.any_tagged) in

  let assertion = Bool.ite can_be_smi tr fl in
  (value, assertion)

(* common: control *)
(* retrieve the value at [idx] from [incoming] *)
(* incoming: | --- idx[0] ---| --- idx[1] --- | --- ... --- | *)
let projection vid idx incoming =
  (* currently, idx of projection is assumebed to be less than 2 *)
  let value = Value.init vid in
  let undefined = idx >= Composed.size_of incoming || idx >= 2 in
  let res =
    if not undefined then Composed.select idx incoming else Value.undefined
  in
  let assertion = Value.is_equal value res in
  (value, assertion)

(* | --- True Condition --- | --- False Condition --- | *)
(* True condition: precond ^ cond *)
(* False condition: precond ^ not cond *)
let branch vid cond precond =
  let value = Composed.init vid 2 in

  let conds_are_bool =
    Bool.ands
      [ Value.has_type Type.bool cond; Value.has_type Type.bool precond ]
  in
  let conds_are_defined =
    Bool.ands [ Value.is_defined cond; Value.is_defined precond ]
  in

  let is_well_defined = Bool.ands [ conds_are_bool; conds_are_defined ] in
  let defined =
    let true_cond = Value.and_ precond cond |> Value.cast Type.bool in
    let false_cond =
      Value.and_ precond (Value.not_ cond) |> Value.cast Type.bool
    in
    Value.is_equal value (BitVec.concat true_cond false_cond)
  in
  let undefined =
    let ubool = Value.undefined |> Value.cast Type.bool in
    Value.is_equal value (BitVec.concat ubool ubool)
  in

  let assertion = Bool.ite is_well_defined defined undefined in
  (value, assertion)

let if_false vid cond =
  let value = Value.init vid in

  let false_cond = cond |> Composed.second_of in
  let cond_is_defined = Value.is_defined false_cond in
  let cond_is_bool = false_cond |> Value.has_type Type.bool in

  let is_well_defined = Bool.ands [ cond_is_defined; cond_is_bool ] in
  let defined = Value.is_equal value false_cond in
  let undefined =
    Value.is_equal value (Value.undefined |> Value.cast Type.bool)
  in

  let assertion = Bool.ite is_well_defined defined undefined in
  (value, assertion)

let if_true vid cond =
  let value = Value.init vid in

  let true_cond = cond |> Composed.first_of in
  let is_cond_defined = Value.is_defined true_cond in
  let is_cond_bool = cond |> Value.has_type Type.bool in

  let is_well_defined = Bool.ands [ is_cond_defined; is_cond_bool ] in
  let defined = Value.is_equal value (cond |> Composed.first_of) in
  let undefined =
    Value.is_equal value (Value.undefined |> Value.cast Type.bool)
  in

  let assertion = Bool.ite is_well_defined defined undefined in
  (value, assertion)

(* merge every incoming execution condition *)
let merge vid conds =
  let value = Composed.init vid (List.length conds) in

  if List.length conds = 0 then (
    print_endline "SB: merge: empty condition list";
    (value, Value.is_equal value (Value.empty |> Value.cast Type.bool)))
  else
    let rec concat_conds res conds =
      match conds with
      | [] -> res
      | cond :: rest -> concat_conds (BitVec.concat res cond) rest
    in

    let assertion =
      Value.is_equal value (concat_conds (List.hd conds) (List.tl conds))
    in
    (value, assertion)

(* common: procedure *)
let parameter vid param =
  let value = Value.init vid in
  let assertion = BitVec.eqb value (param |> Value.cast Type.tagged_signed) in
  (value, assertion)

let return vid return_value =
  let value = Value.init vid in
  let assertion = BitVec.eqb value return_value in
  (value, assertion)
