type options = {
  input_file : string;
  show_lex : bool;
  show_parse : bool;
  show_elab : bool;
}

let usage_msg = "Usage: qdt [options] <file>\n\nOptions:"

let parse_args () =
  let input_file : string option ref = ref None in
  let show_lex : bool ref = ref false in
  let show_parse : bool ref = ref false in
  let show_elab : bool ref = ref false in

  let spec =
    [
      ("--lex", Arg.Set show_lex, " Show lexer output");
      ("--parse", Arg.Set show_parse, " Show parser output");
      ("--elab", Arg.Set show_elab, " Show elaboration output");
    ]
  in

  let anon_fun filename =
    match !input_file with
    | None -> input_file := Some filename
    | Some _ -> raise (Arg.Bad "Multiple files")
  in

  Arg.parse spec anon_fun usage_msg;

  match !input_file with
  | None ->
      Arg.usage spec usage_msg;
      exit 1
  | Some file ->
      {
        input_file = file;
        show_lex = !show_lex;
        show_parse = !show_parse;
        show_elab = !show_elab;
      }
