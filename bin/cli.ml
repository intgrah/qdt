type options = {
  input_file : string;
  show_parse : bool;
  show_elab : string list;
  watch : bool;
}

open Cmdliner

let input_file =
  let doc = "Input file to process" in
  Arg.(required & pos 0 (some string) None & info [] ~docv:"FILE" ~doc)

let show_parse =
  let doc = "Show parser output" in
  Arg.(value & flag & info [ "p"; "parse" ] ~doc)

let show_elab =
  let doc =
    "Print selected definitions after elaboration (comma-separated). Example: \
     -e Nat.rec,Nat"
  in
  let parse (s : string) : string list =
    s |> String.split_on_char ',' |> List.map String.trim
    |> List.filter (fun s -> s <> "")
  in
  let elab_names : string list Arg.conv =
    let parser (s : string) = Ok (parse s) in
    let pp fmt (xs : string list) =
      Format.pp_print_string fmt (String.concat "," xs)
    in
    Arg.conv (parser, pp)
  in
  Arg.(value & opt elab_names [] & info [ "e"; "elab" ] ~docv:"NAMES" ~doc)

let watch =
  let doc = "Watch file for changes" in
  Arg.(value & flag & info [ "w"; "watch" ] ~doc)

let make_options input_file show_parse show_elab watch =
  { input_file; show_parse; show_elab; watch }

let options_term =
  Term.(const make_options $ input_file $ show_parse $ show_elab $ watch)

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
