type options = {
  input_file : string;
  show_lex : bool;
  show_parse : bool;
  show_elab : bool;
  watch : bool;
}

open Cmdliner

let input_file =
  let doc = "Input file to process" in
  Arg.(required & pos 0 (some string) None & info [] ~docv:"FILE" ~doc)

let show_lex =
  let doc = "Show lexer output" in
  Arg.(value & flag & info [ "l"; "lex" ] ~doc)

let show_parse =
  let doc = "Show parser output" in
  Arg.(value & flag & info [ "p"; "parse" ] ~doc)

let show_elab =
  let doc = "Show elaboration output" in
  Arg.(value & flag & info [ "e"; "elab" ] ~doc)

let watch =
  let doc = "Watch file for changes" in
  Arg.(value & flag & info [ "w"; "watch" ] ~doc)

let make_options input_file show_lex show_parse show_elab watch =
  { input_file; show_lex; show_parse; show_elab; watch }

let options_term =
  Term.(
    const make_options $ input_file $ show_lex $ show_parse $ show_elab $ watch)

let cmd =
  let doc = "Dependent type checker" in
  let info = Cmd.info "qdt" ~doc in
  Cmd.v info options_term

let parse_args () =
  match Cmd.eval_value cmd with
  | Ok (`Ok opts) -> opts
  | Ok `Version
  | Ok `Help ->
      exit 0
  | Error _ -> exit 1
