let usage = "Usage: ./jstv [ INPUT_FILE ]"

type conf = {
  target : string;
  emit_graph : bool;
  emit_reduction : bool;
  outdir : string;
}
