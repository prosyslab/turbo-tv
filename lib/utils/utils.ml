let project_root =
  Sys.executable_name |> Filename.dirname |> Filename.dirname
  |> Filename.dirname |> Filename.dirname |> Filename.dirname

let read_lines chan =
  let rec read_lines_tail chan lines =
    try
      let line = input_line chan in
      read_lines_tail chan (line :: lines)
    with End_of_file -> lines
  in
  read_lines_tail chan [] |> List.rev

let write_lines chan lines =
  List.iter (fun line -> output_string chan (line ^ "\n")) lines

let run_d8 target =
  let d8_path = Filename.concat (Filename.concat project_root "d8") "d8" in
  if not (Sys.file_exists d8_path) then failwith "d8 is not exist";

  let cmd =
    String.concat " "
      [ d8_path; "--trace-turbo-reduction"; "--allow-natives-syntax"; target ]
  in
  let chan = Unix.open_process_in cmd in
  Core.In_channel.input_lines chan

let get_nparams target =
  let lines = open_in target |> read_lines in
  let re =
    Re.Pcre.regexp
      "[\\s\\S]*%OptimizeFunctionOnNextCall\\(.*\\);\n.*\\((.*)\\);"
  in
  let params = Re.Group.get (String.concat "\n" lines |> Re.exec re) 1 in
  params |> StringLabels.split_on_char ~sep:',' |> List.length

let pow b e = float_of_int b ** float_of_int e |> int_of_float
