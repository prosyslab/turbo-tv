let project_root =
  Sys.executable_name |> Filename.dirname |> Filename.dirname
  |> Filename.dirname |> Filename.dirname |> Filename.dirname

let usage = "Usage: ./jstv [ INPUT_FILE ]"

type conf = {
  target : string;
  emit_graph : bool;
  emit_reduction : bool;
  outdir : string;
}
