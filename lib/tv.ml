module Stage = State.Stage
module Params = State.Params
module OpcodeSet = State.OpcodeSet
module Objects = Memory.Objects
open ValueOperator
open Z3utils

let ctx = Z3utils.ctx

let validator =
  let init = Tactic.concat [ "simplify"; "eq2bv"; "fpa2bv" ] in
  let qffpbv = Tactic.init "qffpbv" in
  let qfaufbv = Tactic.init "qfaufbv" in
  let smt = Tactic.init "smt" in
  let is_qffpbv = Probe.mk_probe "is-qffpbv" in
  let is_qfaufbv = Probe.mk_probe "is-qfaufbv" in
  let tactic =
    Tactic.and_then init
      (Tactic.cond is_qffpbv qffpbv (Tactic.cond is_qfaufbv qfaufbv smt))
      []
  in
  Solver.init_with_tactic tactic

(* forall param.
   (TaggedSigned(param) \/ HeapNumber(param) \/
    BigInt(param) \/ KnownConstant(param)) *)
let precondition_for_params nparams state =
  let mem = Memory.init nparams in
  let params = Params.init nparams in
  List.mapi
    (fun bid param ->
      Bool.ors
        [
          param |> Value.has_type Type.tagged_signed;
          Bool.ands
            [
              param |> Objects.is_heap_number mem;
              BitVec.eqi (param |> TaggedPointer.off_of) 0;
              BitVec.eqi (param |> TaggedPointer.bid_of) (bid + 1);
            ];
          Bool.ands
            [
              param |> Objects.is_big_int mem;
              BitVec.eqi (param |> TaggedPointer.off_of) 0;
              BitVec.eqi (param |> TaggedPointer.bid_of) (bid + 1);
            ];
          Bool.ands
            [
              param |> Objects.is_string mem;
              BitVec.eqi (param |> TaggedPointer.off_of) 0;
              BitVec.eqi (param |> TaggedPointer.bid_of) (bid + 1);
            ];
          Bool.ors
            (List.map (Value.eq param)
               (RegisterFile.find_all Constant.names state.State.register_file));
        ])
    params
  |> Bool.ands

let check_ub ?(nparams = 2) check_type program =
  let state = Encoder.encode_pgr Stage.Pgm program ~check_type nparams in
  let precond =
    (* precondition_for_params /\ not deopt(pgm) *)
    Bool.ands [ state |> precondition_for_params nparams; Bool.not state.deopt ]
  in
  if State.not_implemented state then (
    Printf.printf "Result: Not Implemented\n";
    Printf.printf "Opcodes: [%s]\n"
      (String.concat ", " (state.not_implemented_opcodes |> OpcodeSet.to_list)))
  else
    (* Check: exists params. precond /\ ub) *)
    let semantic_is_not_uniq =
      program |> Schedule.find_candids
      |> List.fold_left
           (fun res candid ->
             (candid |> Schedule.can_be_overlapped state.access_info) :: res)
           []
      |> Bool.ors
    in
    let ub = Bool.ors [ semantic_is_not_uniq; State.ub state ] in
    let assertion = Bool.ands [ state.assertion; precond; ub ] in
    match Solver.check validator assertion with
    | SATISFIABLE ->
        let model = Option.get (Solver.get_model validator) in
        Printf.printf "Result: Possible\n";
        Printf.printf "Example: \n";
        Printer.print_params model
          (State.register_file state)
          (State.memory state) (State.params state);
        Printer.print_counter_example program state model
    | UNSATISFIABLE -> Printf.printf "Result: Not Possible\n"
    | UNKNOWN -> (
        let reason = Z3.Solver.get_reason_unknown validator in
        match reason with
        | "timeout" -> Printf.printf "Result: Timeout\n"
        | "max. memory exceeded"
        | "smt tactic failed to show goal to be sat/unsat memout" ->
            Printf.printf "Result: Not target\n"
        | _ -> Printf.printf "Result: Unknown\nReason: %s" reason)

let check_eq ?(nparams = 2) src_program tgt_program =
  let src_state = Encoder.encode_pgr Stage.Src src_program nparams in
  let tgt_state = Encoder.encode_pgr Stage.Tgt tgt_program nparams in
  let precond =
    (* precondition_for_params /\ not (deopt(src) \/ deopt(pgm)) *)
    let no_deopt =
      let src_deopt = State.deopt src_state in
      let tgt_deopt = State.deopt tgt_state in
      Bool.not (Bool.ors [ src_deopt; tgt_deopt ])
    in
    Bool.ands [ src_state |> precondition_for_params nparams; no_deopt ]
  in

  let retval_is_same =
    let src_retval = State.retval src_state in
    let tgt_retval = State.retval tgt_state in
    let src_mem = State.memory src_state in
    let tgt_mem = State.memory tgt_state in
    let is_number mem value =
      Bool.ors
        [
          Value.has_type Type.tagged_signed value;
          Bool.ands
            [
              value |> Value.has_type Type.tagged_pointer;
              value |> Objects.is_heap_number mem;
            ];
          Value.has_type Type.float64 value;
        ]
    in
    let is_big_int mem value =
      Bool.ands
        [
          value |> Value.has_type Type.tagged_pointer;
          value |> Objects.is_big_int mem;
        ]
    in
    Bool.ite
      (Bool.ands
         [ src_retval |> is_number src_mem; tgt_retval |> is_number tgt_mem ])
      (Bool.eq
         (src_retval |> Number.to_float64 src_mem)
         (tgt_retval |> Number.to_float64 tgt_mem))
      (Bool.ite
         (Bool.ands
            [
              src_retval |> is_big_int src_mem; tgt_retval |> is_big_int tgt_mem;
            ])
         (let src_big_int = Bigint.load src_retval src_mem in
          let tgt_big_int = Bigint.load tgt_retval tgt_mem in
          Bigint.equal src_big_int tgt_big_int)
         (Bool.eq src_retval tgt_retval))
  in
  if State.not_implemented src_state || State.not_implemented tgt_state then (
    Printf.printf "Result: Not Implemented\n";
    Printf.printf "Opcodes: [%s]\n"
      (String.concat ", "
         (OpcodeSet.union src_state.not_implemented_opcodes
            tgt_state.not_implemented_opcodes
         |> OpcodeSet.to_list)))
  else
    (* Check: exists params. precond /\ not (retval_is_same) *)
    let assertion =
      Bool.ands
        [
          State.assertion src_state;
          State.assertion tgt_state;
          precond;
          Bool.not retval_is_same;
        ]
    in
    match Solver.check validator assertion with
    | SATISFIABLE ->
        let model = Option.get (Solver.get_model validator) in
        Printf.printf "Result: Not Verified \n";
        Printf.printf "CounterExample: \n";
        Printer.print_params model
          (State.register_file src_state)
          (State.memory src_state) (State.params src_state);
        Printer.print_counter_example src_program src_state model;
        Printer.print_counter_example tgt_program tgt_state model
    | UNSATISFIABLE -> Printf.printf "Result: Verified\n"
    | UNKNOWN -> (
        let reason = Z3.Solver.get_reason_unknown validator in
        match reason with
        | "timeout" -> Printf.printf "Result: Timeout\n"
        | "max. memory exceeded"
        | "smt tactic failed to show goal to be sat/unsat memout" ->
            Printf.printf "Result: Not target\n"
        | _ -> Printf.printf "Result: Unknown\nReason: %s" reason)

let print_smt2_query ?(nparams = 2) program =
  let final_state =
    Encoder.encode_pgr Stage.Pgm program ~check_wasm:true nparams
  in
  let precond =
    (* precondition_for_params /\ not (deopt(src) \/ deopt(pgm)) *)
    let no_deopt =
      let deopt = State.deopt final_state in
      Bool.not deopt
    in
    let precond_for_params =
      let params = Params.init nparams in
      List.mapi
        (fun _ param -> Bool.ors [ param |> Value.has_type Type.undefined ])
        params
      |> Bool.ands
    in
    Bool.ands [ no_deopt; precond_for_params ]
  in
  let wasm_assertion =
    let pgm_retval = State.retval final_state in
    let ret = Z3.Expr.mk_const_s ctx "ret" (BV.mk_sort ctx Value.len) in
    Bool.ands [ State.assertion final_state; precond; Bool.eq ret pgm_retval ]
  in

  if State.not_implemented final_state then (
    Printf.printf "Result: Not Implemented\n";
    Printf.printf "Opcodes: [%s]\n"
      (String.concat ", "
         (final_state.not_implemented_opcodes |> OpcodeSet.to_list)))
  else (
    print_endline "final solver query = ";
    wasm_assertion |> Expr.simplify None
    |> Z3.SMT.benchmark_to_smtstring ctx "turbo-tv - SMT query;" "" "" "" []
    |> print_endline)
