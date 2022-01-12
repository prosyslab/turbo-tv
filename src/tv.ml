let check_tv _before_graph_lines _after_graph_lines _desc = ()

let run_tv target parse_graph outdir =
  let lines = open_in target |> Utils.read_lines in
  let reductions = Reduction.get_reductions lines in
  let idx = ref 1 in

  Printf.printf "Number of reductions: %d\n" (List.length reductions);
  List.iter
    (fun (before_graph_lines, after_graph_lines, desc) ->
      if
        String.equal desc
          "- Replacement of #17: Int32Add(32, 33) with #32: \
           CheckedTaggedSignedToInt32[FeedbackSource(INVALID)](2, 14, 41) by \
           reducer MachineOperatorReducer"
      then
        if parse_graph then (
          let before_graph = IR.lines_to_graph before_graph_lines in
          let after_graph = IR.lines_to_graph after_graph_lines in
          let parent = String.concat "/" [ outdir; string_of_int !idx; "" ] in
          Core.Unix.mkdir_p parent ~perm:0o775;

          IR.generate_graph_output (parent ^ "before.dot") before_graph;
          IR.generate_graph_output (parent ^ "after.dot") after_graph);

      idx := !idx + 1;
      check_tv before_graph_lines after_graph_lines desc)
    reductions
