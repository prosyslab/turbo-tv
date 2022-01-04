let read_lines chan =
  let rec read_lines_tail chan lines =
    try
      let line = input_line chan in
      read_lines_tail chan (line :: lines)
    with End_of_file -> lines
  in
  read_lines_tail chan [] |> List.rev

let run_tv filename =
  let lines = open_in filename |> read_lines in
  let reductions = Reduction.get_reductions lines in
  List.iter
    (fun reduction ->
      print_endline "reduction phase";
      List.iter
        (fun (i, line) ->
          print_int i;
          print_char ' ';
          print_endline line)
        reduction)
    reductions

let main () =
  Arg.parse []
    (fun arg ->
      if Sys.file_exists arg then run_tv arg
      else Printf.printf "File \"%s\" does not exist\n" arg)
    Options.usage

let () = main ()