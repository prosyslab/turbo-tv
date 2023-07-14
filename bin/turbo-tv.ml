open Cmdliner
open Lib

type conf = {
  verify : string;
  check_ub : string;
  print_query : string;
  check_type : bool;
  emit_graph : bool;
}

let jstv_args =
  (* Arguments *)
  let verify_arg =
    let doc = "Reduction" in
    Arg.(value & opt string "" & info [ "verify" ] ~docv:"RDC" ~doc)
  in
  let check_ub_arg =
    let doc = "Check whether our system emits UB for the [IR]" in
    Arg.(value & opt file "" & info [ "check-ub" ] ~doc)
  in
  let type_check_arg =
    let doc = "Do check the type for the [SRC]" in
    Arg.(value & flag & info [ "check-type" ] ~doc)
  in
  let emit_graph_arg =
    let doc = "Emit graphs of each reduction step into OUT directory" in
    Arg.(value & flag & info [ "emit-graph" ] ~doc)
  in
  let print_query_arg =
    let doc = "print SMT query for the [IR]" in
    Arg.(value & opt file "" & info [ "print-query" ] ~doc)
  in
  let mk_conf verify check_ub check_type emit_graph print_query =
    { verify; check_ub; check_type; emit_graph; print_query }
  in
  Term.(
    const mk_conf $ verify_arg $ check_ub_arg $ type_check_arg $ emit_graph_arg
    $ print_query_arg)

let parse_command_line () =
  let doc = "Translation validation for TurboFan IR" in
  let info = Cmd.info ~doc "turbo-tv" in
  match Cmd.v info jstv_args |> Cmd.eval_value with
  | Error _ -> exit 1
  | Ok `Version | Ok `Help -> exit 0
  | Ok (`Ok conf) -> conf

let not_target_op_exists pgm =
  (* ignore every program containing 'Loop' or JS operator except the 'JSStackCheck' *)
  IR.G.fold_vertex
    (fun n res ->
      let opcode_str = n |> IR.Node.instr |> Instr.opcode |> Opcode.to_str in
      res
      || opcode_str |> String.starts_with ~prefix:"JS"
         && opcode_str <> "JSStackCheck"
      || Utils.contains opcode_str "Loop")
    pgm false

let main () =
  Printexc.record_backtrace true;
  (* number of parameters (currenty fixed to 2) *)
  let nparams = 2 in
  let { verify; check_ub; check_type; emit_graph; print_query } =
    parse_command_line ()
  in

  if String.length verify <> 0 then
    (* equality check *)
    let src_p, tgt_p =
      if String.contains verify ',' then
        let src_tgt = String.split_on_char ',' verify in
        (List.hd src_tgt, List.nth src_tgt 1)
      else
        let src_p = Filename.concat verify "src.ir" in
        let tgt_p = Filename.concat verify "tgt.ir" in
        (src_p, tgt_p)
    in
    try
      let src = IR.create_from_ir_file src_p in
      let tgt = IR.create_from_ir_file tgt_p in
      if emit_graph then (
        IR.generate_graph_output "source.dot" src;
        IR.generate_graph_output "target.dot" tgt);
      if not_target_op_exists src || not_target_op_exists tgt then
        Printf.printf "Result: Not target\n"
      else Tv.check_eq nparams src tgt
    with
    | Err.NodeNotFound _ ->
        Printf.printf
          "Result: Not target\nReason: invalid graph(node not found)"
    | Err.InvalidBracketArgs _ ->
        Printf.printf "Result: Not target\nReason: invalid graph(bracket args)"
  else if String.length check_ub <> 0 then
    (* undefined behavior check *)
    try
      let pgm_p = check_ub in
      let pgm = IR.create_from_ir_file pgm_p in
      if not_target_op_exists pgm then Printf.printf "Result: Not target\n"
      else Tv.check_ub nparams check_type pgm
    with
    | Err.NodeNotFound _ ->
        Printf.printf
          "Result: Not target\nReason: invalid graph(node not found)"
    | Err.InvalidBracketArgs _ ->
        Printf.printf "Result: Not target\nReason: invalid graph(bracket args)"
  else if String.length print_query <> 0 then
    try
      let pgm_p = print_query in
      let pgm = IR.create_from_ir_file pgm_p in
      if not_target_op_exists pgm then Printf.printf "Result: Not target\n"
      else Tv.print_smt2_query 3 pgm
    with
    | Err.NodeNotFound _ ->
        Printf.printf
          "Result: Not target\nReason: invalid graph(node not found)"
    | Err.InvalidBracketArgs _ ->
        Printf.printf "Result: Not target\nReason: invalid graph(bracket args)"
  else failwith "must give option '--verify' or '--check-ub' or --check-wasm"

let () = main ()