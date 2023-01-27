open Cmdliner
open Lib

type conf = {
  verify : string;
  check_ub : string;
  check_type : bool;
  emit_graph : bool;
}

let jstv_args =
  (* Arguments *)
  let verify_arg =
    let doc = "Reduction" in
    Arg.(value & opt dir "" & info [ "verify" ] ~docv:"RDC" ~doc)
  in

  let check_ub_arg =
    let doc = "Check whether our system emits UB for the [IR]" in
    Arg.(value & opt file "" & info [ "check-ub" ] ~doc)
  in

  let disable_type_check_arg =
    let doc = "Do check the type for the [SRC]" in
    Arg.(value & flag & info [ "check-type" ] ~doc)
  in

  let emit_graph_arg =
    let doc = "Emit graphs of each reduction step into OUT directory" in
    Arg.(value & flag & info [ "emit-graph" ] ~doc)
  in

  let mk_conf verify check_ub check_type emit_graph =
    { verify; check_ub; check_type; emit_graph }
  in

  Term.(
    const mk_conf $ verify_arg $ check_ub_arg $ disable_type_check_arg
    $ emit_graph_arg)

let parse_command_line () =
  let doc = "Translation validation for TurboFan IR" in
  let info = Cmd.info ~doc "turbo-tv" in
  match Cmd.v info jstv_args |> Cmd.eval_value with
  | Error _ -> exit 1
  | Ok `Version | Ok `Help -> exit 0
  | Ok (`Ok conf) -> conf

let not_targeted =
  [
    Opcode.JSAdd;
    JSBitwiseAnd;
    JSBitwiseNot;
    JSBitwiseOr;
    JSBitwiseXor;
    JSCall;
    JSCallForwardVarargs;
    JSCallRuntime;
    JSCallWithArrayLike;
    JSCallWithSpread;
    JSConstruct;
    JSConstructForwardVarargs;
    JSConstructWithArrayLike;
    JSCreateArguments;
    JSCreateArray;
    JSCreateArrayFromIterable;
    JSCreateArrayIterator;
    JSCreateBoundFunction;
    JSCreateCatchContext;
    JSCreateClosure;
    JSCreateEmptyLiteralArray;
    JSCreateEmptyLiteralObject;
    JSCreateFunctionContext;
    JSCreateIterResultObject;
    JSCreateLiteralArray;
    JSCreateLiteralObject;
    JSCreateLiteralRegExp;
    JSCreateObject;
    JSCreatePromise;
    JSCreateTypedArray;
    JSDecrement;
    JSDefineKeyedOwnPropertyInLiteral;
    JSEqual;
    JSExponentiate;
    JSGreaterThan;
    JSGreaterThanOrEqual;
    JSHasInPrototypeChain;
    JSHasProperty;
    JSIncrement;
    JSInstanceOf;
    JSLessThan;
    JSLessThanOrEqual;
    JSLoadContext;
    JSLoadGlobal;
    JSLoadMessage;
    JSLoadNamed;
    JSLoadProperty;
    JSModulus;
    JSMultiply;
    JSOrdinaryHasInstance;
    JSParseInt;
    JSPerformPromiseThen;
    JSRegExpTest;
    JSRejectPromise;
    JSSetKeyedProperty;
    JSSetNamedProperty;
    JSShiftRightLogical;
    JSStoreContext;
    JSStoreGlobal;
    JSStoreMessage;
    JSStoreNamed;
    JSStrictEqual;
    JSToBigIntConvertNumber;
    JSToNumber;
    JSToNumberConvertBigInt;
    JSToNumeric;
    JSToString;
    Loop;
  ]

let unknown_op_exists graph =
  List.exists
    (fun op ->
      try
        IR.find_by_opcode op graph |> ignore;
        true
      with Err.NodeNotFound _ -> false)
    not_targeted

let main () =
  Printexc.record_backtrace true;
  let { verify; check_ub; check_type; emit_graph } = parse_command_line () in
  let nparams = 2 in

  if String.length verify <> 0 then
    let src_ir_p = Filename.concat verify "src.ir" in
    let tgt_ir_p = Filename.concat verify "tgt.ir" in
    try
      let src_grp = IR.create_from_ir_file src_ir_p in
      let tgt_grp = IR.create_from_ir_file tgt_ir_p in
      if emit_graph then (
        IR.generate_graph_output "source.dot" src_grp;
        IR.generate_graph_output "target.dot" tgt_grp);

      if unknown_op_exists src_grp || unknown_op_exists tgt_grp then
        Printf.printf "Result: Not target\n"
      else Tv.run nparams src_grp tgt_grp
    with
    | Err.NodeNotFound _ ->
        Printf.printf
          "Result: Not target\nReason: invalid graph(node not found)"
    | Err.InvalidBracketArgs _ ->
        Printf.printf "Result: Not target\nReason: invalid graph(bracket args)"
  else if String.length check_ub <> 0 then
    try
      let input_ir_p = check_ub in
      let input_grp = IR.create_from_ir_file input_ir_p in
      if unknown_op_exists input_grp then Printf.printf "Result: Not target\n"
      else Tv.check_ub_semantic nparams check_type input_grp
    with
    | Err.NodeNotFound _ ->
        Printf.printf
          "Result: Not target\nReason: invalid graph(node not found)"
    | Err.InvalidBracketArgs _ ->
        Printf.printf "Result: Not target\nReason: invalid graph(bracket args)"
  else failwith "must give option 'verify' or '--check-ub'"

let () = main ()