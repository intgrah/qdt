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
    Format.printf "%a\n\n" Lang.Raw_syntax.pp_program program

let () = main ()
