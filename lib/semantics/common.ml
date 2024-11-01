open Z3utils
open ValueOperator
module ControlTuple = Control.ControlTuple

(* common: constants *)
(* assertion: value = c *)
let float32_constant c state =
  let value = c |> Value.cast Type.float32 in
  state |> State.update ~value

let float64_constant c state =
  let value = c |> Value.cast Type.float64 in
  state |> State.update ~value

let heap_constant name addr mem state =
  let value, mem =
    (* if constant is default constant, use pre-defined value in register file *)
    if Constant.is_constant name then
      (RegisterFile.find name state.State.register_file, mem)
    else if String.starts_with ~prefix:"BigInt" name then
      Bigint.allocate (Bigint.from_string name) mem
    else if Objmap.is_known_map name then
      ( Objmap.map_of name |> BitVec.zero_extend 32
        |> Value.entype Type.map_in_header,
        mem )
    else if String.starts_with ~prefix:"JSFunction" name then
      let fname = List.nth (String.split_on_char ' ' name) 1 in
      let fmap = Hashtbl.hash fname in
      let raw_ptr = TaggedPointer.to_raw_pointer addr in
      let mem =
        Memory.Bytes.store Bool.tr raw_ptr Objmap.size (Objmap.custom_map fmap)
          mem
      in
      (addr, mem)
    else if String.starts_with ~prefix:"String" name then
      Strings.allocate (Strings.from_string name) mem
      (* Angelic TaggedPointer *)
    else if String.starts_with ~prefix:"Object map = " name then
      let tp = addr |> Value.cast Type.tagged_pointer in
      let objmap =
        let pat = Re.Pcre.regexp "Object map = (0x[0-9a-fA-F]*)" in
        try (Re.Group.get (Re.exec pat name) 1 |> int_of_string) land 0xffffffff
        with Not_found -> failwith name
      in
      let mem =
        Memory.Bytes.store Bool.tr
          (TaggedPointer.to_raw_pointer tp)
          Objmap.size (Objmap.custom_map objmap) mem
      in
      (tp, mem)
    else (addr |> Value.cast Type.tagged_pointer, mem)
  in
  state |> State.update ~value ~mem

(* assertion: value = c *)
let int32_constant c state =
  let value = c |> Value.entype Type.int32 in
  state |> State.update ~value

(* behavior: value=c *)
let int64_constant c state =
  let value = c |> Value.entype Type.int64 in
  state |> State.update ~value

(* behavior: value=c *)
let external_constant _c state =
  let value, mem =
    Memory.allocate ~angelic:Bool.tr (Value.from_int 0) state.State.memory
  in
  state |> State.update ~value ~mem

(* behavior: value=c *)
let number_constant c state =
  let is_int_string s =
    try
      int_of_string s |> ignore;
      s <> "-0"
    with Failure _ -> false
  in
  let value =
    if is_int_string c then
      let c_int = int_of_string c in
      if TaggedSigned.lower_limit <= c_int && c_int <= TaggedSigned.upper_limit
      then
        Int.shift_left c_int 1 |> Value.from_int
        |> Value.cast Type.tagged_signed
      else c |> BitVecVal.from_f64string |> Value.entype Type.float64
    else c |> BitVecVal.from_f64string |> Value.entype Type.float64
  in
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
  state |> State.update ~value

(* well-defined condition:
 * - Bool(cond) ^ Bool(precond)
 * - WellDefined(cond) ^ WellDefined(precond)
 * assertion:
 *  ct = ite well-defined (precond ^ cond, precond ^ not cond) (UB, UB) *)
let branch cond precond is_angelic_control state =
  let rf = state.State.register_file in
  let for_false =
    Bool.ors [ Value.is_false cond; Constant.is_false_cst rf cond ]
  in
  let for_true = Bool.not for_false in
  let control =
    ControlTuple.from_tf
      (Bool.and_ precond for_true)
      (Bool.and_ precond for_false)
  in
  state |> State.update ~control ~is_angelic_control

(* well-defined condition:
 * - Bool(FalseCond(cond))
 * - WellDefined(FalseCond(cond))
 * assertion:
 *  ct = ite well-defined FalseCond(Cond) UB *)
let if_false cond is_angelic_control state =
  let control = cond |> ControlTuple.false_cond in
  state |> State.update ~control ~is_angelic_control

(* well-defined condition:
 *  - Bool(TrueCond(cond))
 *  - WellDefined(TrueCond(cond))
 * assertion:
 *  value = ite well-defined TrueCond(Cond) UB *)
let if_true cond is_angelic_control state =
  let control = cond |> ControlTuple.true_cond in
  state |> State.update ~control ~is_angelic_control

(* merge every incoming execution condition *)
let merge conds is_angelic_control state =
  (* cond could be composed value *)
  let control = Bool.ors conds in
  state |> State.update ~control ~is_angelic_control

let phi incomings ctrls state =
  let rec mk_value values conds =
    match values with
    | [ h ] -> Bool.ite (List.hd conds) h Value.empty
    | h :: [ t ] -> Bool.ite (List.hd conds) h t
    | h :: t when List.length t > 1 ->
        Bool.ite (List.hd conds) h (mk_value t (List.tl conds))
    (* length of incoming is larger than 1 *)
    | _ -> failwith "unreachable"
  in
  let value = mk_value incomings ctrls in
  state |> State.update ~value

let select cond tr fl state =
  let value = Bool.ite (Value.is_true cond) tr fl in
  state |> State.update ~value

let throw control state = state |> State.update ~control

let unreachable control control_is_angelic state =
  state |> State.update ~ub:(Bool.ands [ control; Bool.not control_is_angelic ])

(* common: deoptimization *)
let deoptimize _frame _mem control state =
  state |> State.update ~control ~deopt:Bool.tr

let deoptimize_if cond _frame _mem control ctrl_is_angelic state =
  let deopt = Bool.ite (Value.is_true cond) Bool.tr Bool.fl in
  state |> State.update ~control ~deopt ~is_angelic_value:ctrl_is_angelic

let deoptimize_unless cond _frame _mem control ctrl_is_angelic state =
  let deopt = Bool.ite (Value.is_false cond) Bool.tr Bool.fl in
  state |> State.update ~control ~deopt ~is_angelic_value:ctrl_is_angelic

(* common: trap *)
let trap_if control state = state |> State.update ~control

let trap_unless control state = state |> State.update ~control

(* common: procedure *)
let end_ retvals _retmems retctrls state =
  let rec mk_value values conds =
    match values with
    | [ h ] -> Bool.ite (List.hd conds) h Value.empty
    | h :: [ t ] -> Bool.ite (List.hd conds) h t
    | h :: t when List.length t > 1 ->
        Bool.ite (List.hd conds) h (mk_value t (List.tl conds))
    | _ -> failwith "unreachable"
  in
  let value = mk_value retvals retctrls in
  let control = Bool.ors retctrls in
  state |> State.update ~value ~control ~final:true

let parameter param state =
  let value = param in
  state |> State.update ~value

let return return_value return_control state =
  (* return heap number or smi or bool *)
  let rf = State.register_file state in
  let true_constant = RegisterFile.find "true" rf in
  let false_constant = RegisterFile.find "false" rf in
  let value =
    Bool.ite
      (return_value |> Value.has_type Type.float64)
      return_value
      (Bool.ite
         (return_value |> Value.has_type Type.tagged_pointer)
         return_value
         (Bool.ite
            (return_value |> Value.has_type Type.bool)
            (Bool.ite
               (Value.eq Value.tr return_value)
               true_constant false_constant)
            (return_value |> Value.cast Type.tagged_signed)))
  in
  state |> State.update ~value ~control:return_control

let return_wasm return_value return_control state =
  let value = return_value in
  state |> State.update ~value ~control:return_control

let start state = state |> State.update ~control:Bool.tr

(* common: region *)
let finish_region pval state = state |> State.update ~value:pval

(* temporary *)
let js_call n_input fname state =
  if fname = "startsWith" then
    if n_input <= 3 then state |> State.update ~value:Value.tr ~control:Bool.tr
    else failwith "not implemented"
  else failwith "not implemented"

let js_stack_check _eff control state = state |> State.update ~control

let call fname n_return args control state =
  let return_sort = BV.mk_sort ctx (Value.len * n_return) in
  let arg_sort = BV.mk_sort ctx Value.len in
  let args_sort = List.map (fun _ -> arg_sort) args in
  let f_decl = Z3.FuncDecl.mk_func_decl_s ctx fname args_sort return_sort in
  let normalized_args =
    let mem = state.State.memory in
    args
    |> List.map (fun arg ->
           if Strings.is_string arg mem = true then arg
           else
             Bool.ite
               (* TaggedSigned | HeapNumber | Int32 | Uint32 | Float64 *)
               (Number.is_number arg mem)
               (arg |> Number.to_float64 mem)
               (* Int64 *)
               (Bool.ite
                  (arg |> Value.has_type Type.int64)
                  (Int64.div arg (Int64.of_int 2) |> Int64.to_float64)
                  (Bool.ite
                     (* BigInt *)
                     (arg |> Memory.Objects.is_big_int mem)
                     ((Bigint.load arg mem).value |> Value.entype Type.int64)
                     arg)))
  in
  let return = Z3.FuncDecl.apply f_decl normalized_args in
  let value =
    if n_return = 1 then
      return |> Value.cast Type.any_tagged |> ValueOperator.AnyTagged.settle
    else
      return |> Composed.to_list
      |> List.map (fun v ->
             v |> Value.cast Type.any_tagged |> ValueOperator.AnyTagged.settle)
      |> Composed.from_values
  in
  let is_angelic_value = Bool.tr in
  state |> State.update ~value ~control ~is_angelic_value

let stack_pointer_greater_than state =
  state |> State.update ~value:Value.tr ~control:Bool.tr
(* temporary-over *)
