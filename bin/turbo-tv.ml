open Cmdliner
open Lib

type conf = {
  target : string option;
  test_unit : (string * string) option;
  emit_graph : bool;
  emit_reduction : bool;
  outdir : string;
}

let jstv_args =
  (* Arguments *)
  let target_arg =
    let doc = "Target JS for translation validation." in
    Arg.(value & pos 0 (some string) None & info [] ~docv:"JS" ~doc)
  in

  let test_unit_arg =
    let doc = "Test on unit (src IR & target IR)" in
    Arg.(
      value & opt (list ~sep:',' file) [] & info [ "test" ] ~docv:"TEST" ~doc)
  in

  let emit_graph_arg =
    let doc = "Emit graphs of each reduction step into OUT directory" in
    Arg.(value & flag & info [ "emit-graph" ] ~doc)
  in

  let emit_reduction_arg =
    let doc = "Emit reductions of each step into OUT/[id]/reduction.txt" in
    Arg.(value & flag & info [ "emit-reduction" ] ~doc)
  in

  let outdir_arg =
    let doc = "Output directory" in
    Arg.(value & opt string "./out" & info [ "o"; "out" ] ~docv:"OUTDIR" ~doc)
  in

  let mk_conf target test_unit emit_graph emit_reduction outdir =
    let test_unit =
      if List.length test_unit = 2 then
        Some (List.nth test_unit 0, List.nth test_unit 1)
      else None
    in
    { target; test_unit; emit_graph; emit_reduction; outdir }
  in

  Term.(
    const mk_conf $ target_arg $ test_unit_arg $ emit_graph_arg
    $ emit_reduction_arg $ outdir_arg)

let parse_command_line () =
  let doc = "Translation validation for TurboFan IR" in
  let info = Cmd.info ~doc "turbo-tv" in
  match Cmd.v info jstv_args |> Cmd.eval_value with
  | Error _ -> exit 1
  | Ok `Version | Ok `Help -> exit 0
  | Ok (`Ok conf) -> conf

let jscall_exists graph =
  let jscall = Opcode.JSCall in
  try
    IR.find_by_opcode jscall graph |> ignore;
    true
  with Err.NodeNotFound _ -> false

let main () =
  Printexc.record_backtrace true;
  let { target; test_unit; emit_reduction; emit_graph; outdir } =
    parse_command_line ()
  in

  if Option.is_some test_unit then
    let src_ir_f, tgt_ir_f = test_unit |> Option.get in
    let src_grp = IR.create_from_ir_file src_ir_f in
    let tgt_grp = IR.create_from_ir_file tgt_ir_f in
    let src_cfg = IR.get_control_flow_graph src_grp in
    let tgt_cfg = IR.get_control_flow_graph tgt_grp in
    (* for now, set number of parameters for testing 100 *)
    let nparams = 100 in
    Tv.run nparams src_grp tgt_grp src_cfg tgt_cfg
  else
    let target =
      try Option.get target
      with Invalid_argument _ -> failwith "No target specified"
    in
    let nparams = Utils.get_nparams target in
    let lines = Utils.run_d8 target in
    let idx = ref 1 in
    let reductions =
      Reduction.get_reductions lines
      |> List.map (fun (src_ir, tgt_ir, desc) ->
             let src_grp = IR.create_from src_ir in
             let tgt_grp = IR.create_from tgt_ir in
             ((src_ir, src_grp), (tgt_ir, tgt_grp), desc))
      |> List.filter (fun ((_, before_graph), (_, after_graph), _) ->
             (not (jscall_exists before_graph))
             && not (jscall_exists after_graph))
    in
    Printf.printf "Number of reductions: %d\n" (List.length reductions);
    List.iter
      (fun rdc ->
        let (src_ir, src_grp), (tgt_ir, tgt_grp), desc = rdc in
        Printf.printf "Reduction #%d: " !idx;
        Printf.printf "%s\n" desc;

        let src_cfg = IR.get_control_flow_graph src_grp in
        let tgt_cfg = IR.get_control_flow_graph tgt_grp in

        if emit_reduction then (
          let parent = String.concat "/" [ outdir; string_of_int !idx; "" ] in
          Core_unix.mkdir_p parent ~perm:0o775;
          let src_out_chan = open_out (parent ^ "before.txt") in
          let tgt_out_chan = open_out (parent ^ "after.txt") in

          src_ir |> Utils.write_lines src_out_chan;
          tgt_ir |> Utils.write_lines tgt_out_chan);

        if emit_graph then (
          let parent = String.concat "/" [ outdir; string_of_int !idx; "" ] in
          Core_unix.mkdir_p parent ~perm:0o775;

          IR.generate_graph_output (parent ^ "before_cfg.dot") src_cfg;
          IR.generate_graph_output (parent ^ "after_cfg.dot") tgt_cfg;

          IR.generate_graph_output (parent ^ "before.dot") src_grp;
          IR.generate_graph_output (parent ^ "after.dot") tgt_grp);
        Tv.run nparams src_grp tgt_grp src_cfg tgt_cfg;
        idx := !idx + 1;
        print_newline ())
      reductions

let () = main ()
