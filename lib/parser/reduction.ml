let special_prefix = "- "

let in_place_prefix = "- In-place update"

let lowering_prefix = "- Simplified Lowering"

let replacement_prefix = "- Replacement"

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
  || String.starts_with ~prefix:lowering_prefix line
  || String.starts_with ~prefix:replacement_prefix line

let get_indices_and_desc reduction =
  let before_graph_start = List.nth reduction 0 |> fst in
  let before_graph_end = List.nth reduction 1 |> fst in
  let after_graph_start = List.nth reduction 3 |> fst in
  let after_graph_end = List.nth reduction 4 |> fst in
  let desc = List.nth reduction 2 |> snd in
  ( before_graph_start,
    before_graph_end,
    after_graph_start,
    after_graph_end,
    desc )

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
  let lines_with_ind = lines |> List.mapi (fun i line -> (i, line)) in
  List.map
    (fun reduction ->
      let ( before_graph_start,
            before_graph_end,
            after_graph_start,
            after_graph_end,
            desc ) =
        get_indices_and_desc reduction
      in
      let before_graph_lines =
        lines_with_ind
        |> List.filteri (fun i _ ->
               before_graph_start < i && i < before_graph_end)
        |> List.map (fun (_, line) -> line)
      in
      let after_graph_lines =
        lines_with_ind
        |> List.filteri (fun i _ ->
               after_graph_start < i && i < after_graph_end)
        |> List.map (fun (_, line) -> line)
      in
      (before_graph_lines, after_graph_lines, desc))
    (List.rev reductions)
