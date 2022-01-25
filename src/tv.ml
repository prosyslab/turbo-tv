open Options

let check_tv before_graph_lines after_graph_lines params =
  let before_graph = IR.create_from before_graph_lines in
  let before_graph_return_value =
    Semantics.get_return_value before_graph_lines before_graph params
  in
  let after_graph = IR.create_from after_graph_lines in
  let after_graph_return_value =
    Semantics.get_return_value after_graph_lines after_graph params
  in
  if before_graph_return_value = after_graph_return_value then
    print_endline "check_tv success!"
  else print_endline "check_tv fail..."

let run_d8 target =
  let d8_path = Filename.concat (Filename.concat project_root "d8") "d8" in
  if not (Sys.file_exists d8_path) then failwith "d8 is not exist";

  let cmd =
    String.concat " "
      [ d8_path; "--trace-turbo-reduction"; "--allow-natives-syntax"; target ]
  in
  let chan = Unix.open_process_in cmd in
  Core.In_channel.input_lines chan

let get_params target =
  let lines = open_in target |> Utils.read_lines in
  let re =
    Re.Pcre.regexp
      "[\\s\\S]*%OptimizeFunctionOnNextCall\\(.*\\);\n.*\\((.*)\\);"
  in
  let params = Re.Group.get (String.concat "\n" lines |> Re.exec re) 1 in
  params |> StringLabels.split_on_char ~sep:',' |> List.map String.trim

let run_tv conf =
  let { target; emit_reduction; emit_graph; outdir } = conf in

  let lines = run_d8 target in
  let params = get_params target in
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
          let before_graph = IR.create_from before_graph_lines in
          let after_graph = IR.create_from after_graph_lines in
          let parent = String.concat "/" [ outdir; string_of_int !idx; "" ] in
          Core.Unix.mkdir_p parent ~perm:0o775;

          IR.generate_graph_output (parent ^ "before.dot") before_graph;
          IR.generate_graph_output (parent ^ "after.dot") after_graph));
      idx := !idx + 1;
      check_tv before_graph_lines after_graph_lines params;
      print_newline ())
    reductions
