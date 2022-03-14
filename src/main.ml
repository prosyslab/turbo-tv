open Cmdliner

type conf = {
  target : string;
  emit_graph : bool;
  emit_reduction : bool;
  outdir : string;
}

let jstv_args =
  (* Arguments *)
  let target_arg =
    let doc = "Target for translation validation." in
    Arg.(required & pos 0 (some string) None & info [] ~docv:"TARGET" ~doc)
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

  let mk_conf target emit_graph emit_reduction outdir =
    { target; emit_graph; emit_reduction; outdir }
  in
  Term.(
    const mk_conf $ target_arg $ emit_graph_arg $ emit_reduction_arg
    $ outdir_arg)

let parse_command_line () =
  let doc = "Translation validation for TurboFan IR" in
  let info = Cmd.info ~doc "turbo-tv" in
  match Cmd.v info jstv_args |> Cmd.eval_value with
  | Error _ -> exit 1
  | Ok `Version | Ok `Help -> exit 0
  | Ok (`Ok conf) -> conf

let main () =
  Printexc.record_backtrace true;
  let { target; emit_reduction; emit_graph; outdir } = parse_command_line () in

  let nparams = Utils.get_nparams target in
  let lines = Utils.run_d8 target in
  let reductions = Reduction.get_reductions lines in
  let idx = ref 1 in

  Printf.printf "Number of reductions: %d\n" (List.length reductions);
  List.iter
    (fun (before_rdc, after_rdc, _desc) ->
      Printf.printf "Reduction #%d: " !idx;
      let before_graph = IR.create_from before_rdc in
      let after_graph = IR.create_from after_rdc in
      if emit_reduction then (
        let parent = String.concat "/" [ outdir; string_of_int !idx; "" ] in
        Core.Unix.mkdir_p parent ~perm:0o775;
        let before_out_chan = open_out (parent ^ "before.txt") in
        let after_out_chan = open_out (parent ^ "after.txt") in

        before_rdc |> Utils.write_lines before_out_chan;
        after_rdc |> Utils.write_lines after_out_chan);

      if emit_graph then (
        let parent = String.concat "/" [ outdir; string_of_int !idx; "" ] in
        Core.Unix.mkdir_p parent ~perm:0o775;

        IR.generate_graph_output (parent ^ "before.dot") before_graph;
        IR.generate_graph_output (parent ^ "after.dot") after_graph);
      Tv.run nparams before_graph after_graph;
      idx := !idx + 1;
      print_newline ())
    reductions

let () = main ()
