open Cmdliner

type conf = { target : string; parse_graph : bool; outdir : string }

let jstv_args =
  (* Arguments *)
  let target_arg =
    let doc = "Target for translation validation." in
    Arg.(required & pos 0 (some string) None & info [] ~docv:"TARGET" ~doc)
  in

  let parse_graph_arg =
    let doc = "Generate parsed graph into OUT directory" in
    Arg.(value & flag & info [ "parse-graph" ] ~doc)
  in

  let outdir_arg =
    let doc = "Output directory" in
    Arg.(value & opt string "./out" & info [ "o"; "out" ] ~docv:"OUTDIR" ~doc)
  in

  let mk_conf target parse_graph outdir = { target; parse_graph; outdir } in
  Term.(const mk_conf $ target_arg $ parse_graph_arg $ outdir_arg)

let parse_command_line () =
  let doc = "Translation validation for TurboFan IR" in
  let info = Term.info ~doc "turbo-tv" in
  match Term.eval (jstv_args, info) with
  | `Error _ -> exit 1
  | `Version | `Help -> exit 0
  | `Ok conf -> conf

let main () =
  Printexc.record_backtrace true;
  let conf = parse_command_line () in
  let res = Tv.run_tv conf.target conf.parse_graph conf.outdir in

  try res with
  | Failure msg ->
      Printf.eprintf "Error: %s\n%!" msg;
      exit 1
  | e ->
      let trace = Printexc.get_backtrace () in
      Printf.eprintf "Error: exception %s\n%s%!" (Printexc.to_string e) trace

let () = main ()
