let read_lines chan =
  let rec read_lines_tail chan lines =
    try
      let line = input_line chan in
      read_lines_tail chan (line :: lines)
    with End_of_file -> lines
  in
  read_lines_tail chan [] |> List.rev

let check_tv before_graph_lines after_graph_lines _desc =
  let before_graph = IR.lines_to_graph before_graph_lines in
  let after_graph = IR.lines_to_graph after_graph_lines in
  IR.generate_graph_output "before.dot" before_graph;
  IR.generate_graph_output "after.dot" after_graph

let run_tv filename =
  let lines = open_in filename |> read_lines in
  let reductions = Reduction.get_reductions lines in
  List.iter
    (fun (before_graph_lines, after_graph_lines, desc) ->
      if
        String.equal desc
          "- Replacement of #17: Int32Add(32, 33) with #32: \
           CheckedTaggedSignedToInt32[FeedbackSource(INVALID)](2, 14, 41) by \
           reducer MachineOperatorReducer"
      then check_tv before_graph_lines after_graph_lines desc)
    reductions

let main () =
  Arg.parse []
    (fun arg ->
      if Sys.file_exists arg then run_tv arg
      else Printf.printf "File \"%s\" does not exist\n" arg)
    Options.usage

let () = main ()