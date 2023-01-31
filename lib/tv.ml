module Params = State.Params
module HeapNumber = Objects.HeapNumber
module OpcodeSet = State.OpcodeSet
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

let check_ub_semantic nparams check_type program =
  let state = Encoder.encode_pgr "test" program ~check_type nparams in
  let ub = State.ub state in
  let mem = State.memory state in
  (* params are tagged /\ not deopt *)
  let precond =
    let params = State.params state in
    let params_are_smi_or_heapnumber_or_bigint =
      List.mapi
        (fun bid param ->
          Bool.ors
            [
              param |> Value.has_type Type.tagged_signed;
              Bool.ands
                [
                  param |> Objects.is_heap_number mem;
                  BitVec.eqi (param |> TaggedPointer.off_of) 0;
                  (* bid 0 is reserved for referenced angelic ptr *)
                  BitVec.eqi (param |> TaggedPointer.bid_of) (bid + 1);
                ];
              Bool.ands
                [
                  param |> Objects.is_big_int mem;
                  BitVec.eqi (param |> TaggedPointer.off_of) 0;
                  BitVec.eqi (param |> TaggedPointer.bid_of) (bid + 1);
                ];
              Bool.ors
                (List.map (Value.eq param)
                   (RegisterFile.find_all Constant.names state.register_file));
            ])
        params
      |> Bool.ands
    in
    Bool.ands [ params_are_smi_or_heapnumber_or_bigint; Bool.not state.deopt ]
  in
  let assertion = Bool.ands [ state.assertion; precond; ub ] in

  if State.not_implemented state then (
    Printf.printf "Result: Not Implemented\n";
    Printf.printf "Opcodes: [%s]\n"
      (String.concat ", " (state.not_implemented_opcodes |> OpcodeSet.to_list)))
  else
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
    | UNKNOWN ->
        let reason = Z3.Solver.get_reason_unknown validator in
        Printf.printf "Result: Unknown\nReason: %s" reason

let run nparams src_program tgt_program =
  let src_state = Encoder.encode_pgr "before" src_program nparams in
  let tgt_state = Encoder.encode_pgr "after" tgt_program nparams in

  (* params are tagged /\ not deopt *)
  let precond =
    let params = State.params src_state in
    let mem = Memory.init nparams in
    let params_are_smi_or_heapnumber_or_bigint =
      List.mapi
        (fun bid param ->
          Bool.ors
            [
              param |> Value.has_type Type.tagged_signed;
              Bool.ands
                [
                  param |> Objects.is_heap_number mem;
                  BitVec.eqi (param |> TaggedPointer.off_of) 0;
                  (* bid 0 is reserved for referenced angelic ptr *)
                  BitVec.eqi (param |> TaggedPointer.bid_of) (bid + 1);
                ];
              Bool.ands
                [
                  param |> Objects.is_big_int mem;
                  BitVec.eqi (param |> TaggedPointer.off_of) 0;
                  BitVec.eqi (param |> TaggedPointer.bid_of) (bid + 1);
                ];
              Bool.ors
                (List.map (Value.eq param)
                   (RegisterFile.find_all Constant.names src_state.register_file));
            ])
        params
      |> Bool.ands
    in
    let no_deopt =
      let src_deopt = State.deopt src_state in
      let tgt_deopt = State.deopt tgt_state in
      Bool.not (Bool.ors [ src_deopt; tgt_deopt ])
    in
    Bool.ands [ params_are_smi_or_heapnumber_or_bigint; no_deopt ]
  in

  let retval_is_same =
    let src_retval = State.retval src_state in
    let src_mem = State.memory src_state in
    let tgt_retval = State.retval tgt_state in
    let tgt_mem = State.memory tgt_state in

    let is_tagged_signed_or_heap_number_or_float64 mem value =
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
         [
           src_retval |> is_tagged_signed_or_heap_number_or_float64 src_mem;
           tgt_retval |> is_tagged_signed_or_heap_number_or_float64 tgt_mem;
         ])
      (Bool.eq
         (src_retval |> Number.to_float64 src_mem)
         (tgt_retval |> Number.to_float64 tgt_mem))
      (Bool.ite
         (Bool.ands
            [ is_big_int src_mem src_retval; is_big_int tgt_mem tgt_retval ])
         (let src_big_int = Bigint.load src_retval src_mem in
          let tgt_big_int = Bigint.load tgt_retval tgt_mem in
          Bigint.equal src_big_int tgt_big_int)
         (Bool.eq src_retval tgt_retval))
  in

  let assertion =
    Bool.ands
      [
        State.assertion src_state;
        State.assertion tgt_state;
        precond;
        Bool.not retval_is_same;
      ]
  in

  let is_not_implemented =
    State.not_implemented src_state || State.not_implemented tgt_state
  in

  if is_not_implemented then (
    Printf.printf "Result: Not Implemented\n";
    Printf.printf "Opcodes: [%s]\n"
      (String.concat ", "
         (OpcodeSet.union src_state.not_implemented_opcodes
            tgt_state.not_implemented_opcodes
         |> OpcodeSet.to_list)))
  else
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
    | UNKNOWN ->
        let reason = Z3.Solver.get_reason_unknown validator in
        Printf.printf "Result: Unknown\nReason: %s\n" reason
