let main () =
  let args = Cli.parse_args () in

  let src = In_channel.with_open_text args.input_file In_channel.input_all in
  let src_chars = String.to_seq src |> List.of_seq in

  (* Lex *)
  let tokens = Elaboration.Lexer.scan [] src_chars in
  if args.show_lex then
    Format.printf "%a\n\n"
      (Format.pp_print_list
         ~pp_sep:(fun fmt () -> Format.fprintf fmt " ")
         Elaboration.Lexer.pp_token)
      tokens;

  (* Parse *)
  let program =
    try Elaboration.Parser.parse tokens with
    | Elaboration.Parser.Parse_error msg ->
        Format.printf "Parse error: %s\n" msg;
        exit 1
    | Elaboration.Parser.Tokens_remaining remaining ->
        let remaining_str =
          let buf = Buffer.create 100 in
          let fmt = Format.formatter_of_buffer buf in
          List.iteri
            (fun i t ->
              if i < 5 then (
                if i > 0 then
                  Format.fprintf fmt " ";
                Format.fprintf fmt "%a" Elaboration.Lexer.pp_token t))
            remaining;
          Format.pp_print_flush fmt ();
          Buffer.contents buf
        in
        Format.printf "Parse error: Unexpected tokens remaining: %s%s\n"
          remaining_str
          (if List.length remaining > 5 then
             "..."
           else
             "");
        exit 1
  in
  if args.show_parse then
    Format.printf "%a\n\n" Elaboration.Pretty.pp_raw_program program;

  (* Elaborate *)
  try
    let elab_defs = Elaboration.Elab.elab_program program in
    if args.show_elab then
      List.iter
        (fun def -> Format.printf "%a@.@." Elaboration.Pretty.pp_def def)
        elab_defs
  with
  | Elaboration.Elab.Elab_error msg ->
      Format.printf "Elaboration error: %s\n" msg;
      exit 1
  | e ->
      Format.printf "Unexpected error: %s\n" (Printexc.to_string e);
      exit 1

let () = main ()
