open Cmdliner
open Lib

type conf = {
  source : string option;
  target : string option;
  check_ub : bool;
  check_type : bool;
  emit_graph : bool;
}

let jstv_args =
  (* Arguments *)
  let source_arg =
    let doc = "Source IR" in
    Arg.(value & pos 0 (some string) None & info [] ~docv:"SRC" ~doc)
  in

  let target_arg =
    let doc = "Target IR" in
    Arg.(value & pos 1 (some string) None & info [] ~docv:"TGT" ~doc)
  in

  let check_ub_arg =
    let doc = "Check whether our system emits UB for the [SRC]" in
    Arg.(value & flag & info [ "check-ub" ] ~doc)
  in

  let disable_type_check_arg =
    let doc = "Do check the type for the [SRC]" in
    Arg.(value & flag & info [ "check-type" ] ~doc)
  in

  let emit_graph_arg =
    let doc = "Emit graphs of each reduction step into OUT directory" in
    Arg.(value & flag & info [ "emit-graph" ] ~doc)
  in

  let mk_conf source target check_ub check_type emit_graph =
    { source; target; check_ub; check_type; emit_graph }
  in

  Term.(
    const mk_conf $ source_arg $ target_arg $ check_ub_arg
    $ disable_type_check_arg $ emit_graph_arg)

let parse_command_line () =
  let doc = "Translation validation for TurboFan IR" in
  let info = Cmd.info ~doc "turbo-tv" in
  match Cmd.v info jstv_args |> Cmd.eval_value with
  | Error _ -> exit 1
  | Ok `Version | Ok `Help -> exit 0
  | Ok (`Ok conf) -> conf

let unknown_ops =
  [
    Opcode.JSCall;
    Opcode.JSAdd;
    Opcode.JSModulus;
    Opcode.JSEqual;
    Opcode.JSDecrement;
    Opcode.JSLoadContext;
    Opcode.JSCallRuntime;
    Opcode.JSStrictEqual;
    Opcode.JSLessThan;
    Opcode.JSLessThanOrEqual;
    Opcode.JSGreaterThanOrEqual;
    Opcode.JSLoadGlobal;
    Opcode.JSBitwiseOr;
    Opcode.JSBitwiseAnd;
    Opcode.JSBitwiseNot;
    Opcode.JSBitwiseXor;
    Opcode.JSExponentiate;
    Opcode.JSMultiply;
    Opcode.JSGreaterThan;
    Opcode.JSToNumeric;
    Opcode.JSShiftRightLogical;
    Opcode.JSStoreContext;
    Opcode.JSCreateEmptyLiteralArray;
    Opcode.JSToNumber;
    Opcode.JSIncrement;
    Opcode.Loop;
  ]

let unknown_op_exists graph =
  List.exists
    (fun op ->
      try
        IR.find_by_opcode op graph |> ignore;
        true
      with Err.NodeNotFound _ -> false)
    unknown_ops

let main () =
  Printexc.record_backtrace true;
  let { source; target; check_ub; check_type; emit_graph } =
    parse_command_line ()
  in
  let nparams = 2 in

  if not check_ub then (
    let src_ir_p = source |> Option.get in
    let tgt_ir_p = target |> Option.get in
    let src_grp = IR.create_from_ir_file src_ir_p in
    let tgt_grp = IR.create_from_ir_file tgt_ir_p in

    if emit_graph then (
      IR.generate_graph_output "source.dot" src_grp;
      IR.generate_graph_output "target.dot" tgt_grp);

    if unknown_op_exists src_grp || unknown_op_exists tgt_grp then
      Printf.printf "Result: Not target\n"
    else Tv.run nparams src_grp tgt_grp)
  else
    let test_ir_p = source |> Option.get in
    let test_grp = IR.create_from_ir_file test_ir_p in
    if unknown_op_exists test_grp then Printf.printf "Result: Not target\n"
    else Tv.check_ub_semantic nparams check_type test_grp

let () = main ()