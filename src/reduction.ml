let special_prefix = "- "
let in_place_prefix = "- In-place update"
let replacement_prefix = "- Replacement"
let graph_start_prefix = "- Start Graph"
let graph_end_prefix = "- End Graph"

let extract_special_lines lines =
  lines
  |> List.mapi (fun i line -> (i, line))
  |> List.filter (fun (_, line) ->
         String.starts_with ~prefix:special_prefix line)

let update_reductions line_info reductions =
  let less_than_five, others =
    List.partition (fun reduction -> List.length reduction < 5) reductions
  in
  List.concat
    [
      [ [ line_info ] ];
      others;
      less_than_five |> List.map (fun reduction -> line_info :: reduction);
    ]

let is_reduction_occur line =
  String.starts_with ~prefix:in_place_prefix line
  || String.starts_with ~prefix:replacement_prefix line

let get_reductions lines =
  let special_lines = extract_special_lines lines in
  let reductions =
    List.fold_right
      (fun line_info reductions -> update_reductions line_info reductions)
      special_lines []
    |> List.filter (fun reduction -> List.length reduction = 5)
    |> List.filter (fun reduction ->
           let center = List.nth reduction 2 |> snd in
           is_reduction_occur center)
  in
  reductions