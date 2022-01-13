open Options

let check_tv _before_graph_lines _after_graph_lines _desc = ()

let run_tv conf =
  let { target; emit_reduction; emit_graph; outdir } = conf in

  let lines = open_in target |> Utils.read_lines in
  let reductions = Reduction.get_reductions lines in
  let idx = ref 1 in

  Printf.printf "Number of reductions: %d\n" (List.length reductions);
  List.iter
    (fun (before_graph_lines, after_graph_lines, desc) ->
      Printf.printf "Validate reduction #%d\n" !idx;
      Printf.printf "%s\n" desc;
      if
        String.equal desc
          "- Replacement of #17: Int32Add(32, 33) with #32: \
           CheckedTaggedSignedToInt32[FeedbackSource(INVALID)](2, 14, 41) by \
           reducer MachineOperatorReducer"
      then (
        if emit_reduction then (
          let parent = String.concat "/" [ outdir; string_of_int !idx; "" ] in
          Core.Unix.mkdir_p parent ~perm:0o775;
          let before_out_chan = open_out (parent ^ "before.txt") in
          let after_out_chan = open_out (parent ^ "after.txt") in

          before_graph_lines |> Utils.write_lines before_out_chan;
          after_graph_lines |> Utils.write_lines after_out_chan);

        if emit_graph then (
          let before_graph = IR.lines_to_graph before_graph_lines in
          let after_graph = IR.lines_to_graph after_graph_lines in
          let parent = String.concat "/" [ outdir; string_of_int !idx; "" ] in
          Core.Unix.mkdir_p parent ~perm:0o775;

          IR.generate_graph_output (parent ^ "before.dot") before_graph;
          IR.generate_graph_output (parent ^ "after.dot") after_graph));
      idx := !idx + 1;
      check_tv before_graph_lines after_graph_lines desc;
      print_newline ())
    reductions
