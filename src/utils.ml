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
