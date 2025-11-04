let main () =
  let args = Cli.parse_args () in

  let src = In_channel.with_open_text args.input_file In_channel.input_all in
  let src_chars = String.to_seq src |> List.of_seq in

  (* Lex *)
  let tokens = Lang.Lexer.scan [] src_chars in
  if args.show_lex then
    Format.printf "%a\n\n"
      (Format.pp_print_list
         ~pp_sep:(fun fmt () -> Format.fprintf fmt " ")
         Lang.Token.pp)
      tokens;

  (* Parse *)
  let program = Lang.Parser.parse tokens in
  if args.show_parse then
    Format.printf "%a\n\n" Lang.Raw_syntax.pp_program program;

  (* Elaborate *)
  if args.show_elab then
    try
      let elab_defs = Elaboration.Elab.elab_program program in
      List.iter
        (fun (name, term, ty) ->
          Format.printf "%s\n" name;
          Format.printf "Type: %a\n" Elaboration.Pretty.pp_ty_val ty;
          Format.printf "Term: %a\n\n" Elaboration.Pretty.pp_tm term)
        elab_defs
    with
    | Elaboration.Elab.Elab_error msg ->
        Format.printf "Elaboration error: %s\n" msg
    | e -> Format.printf "Unexpected error: %s\n" (Printexc.to_string e)

let () = main ()
