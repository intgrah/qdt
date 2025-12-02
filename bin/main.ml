module Pipeline = Elaboration.Incr
module Update = Pipeline.Update

let poll_seconds = 0.1

let read_file path =
  try Some (In_channel.with_open_text path In_channel.input_all) with
  | Sys_error msg ->
      Format.eprintf "Failed to read %s: %s@." path msg;
      None

let read_file_exn path =
  match read_file path with
  | Some contents -> contents
  | None -> exit 1

let log_stage stage = function
  | Update.Initialized _ -> Format.eprintf "[inc] %s initialized@." stage
  | Update.Changed _ -> Format.eprintf "[inc] %s changed@." stage
  | Update.Invalidated -> Format.eprintf "[inc] %s invalidated@." stage

let print_tokens tokens =
  Format.printf "%a@."
    (Format.pp_print_list
       ~pp_sep:(fun fmt () -> Format.fprintf fmt " ")
       Elaboration.Lexer.pp_token)
    tokens

let print_program program =
  Format.printf "%a@." Elaboration.Pretty.pp_raw_program program

let print_defs defs =
  List.iter
    (fun def -> Format.printf "%a@.@." Elaboration.Pretty.pp_def def)
    defs

let handle_stage_result ~show ~printer = function
  | Update.Initialized (Ok value)
  | Update.Changed (_, Ok value) ->
      if show then
        printer value
  | Update.Initialized (Error err)
  | Update.Changed (_, Error err) ->
      Format.printf "%s@." (Pipeline.string_of_stage_error err)
  | Update.Invalidated -> ()

let rec watch_loop file pipeline last_mtime =
  Unix.sleepf poll_seconds;
  let last_mtime =
    match Unix.stat file with
    | exception Unix.Unix_error (err, _, _) ->
        Format.eprintf "Error: %s" (Unix.error_message err);
        last_mtime
    | stats ->
        if stats.st_mtime > last_mtime then (
          match
            read_file file
          with
          | None -> last_mtime
          | Some contents ->
              Pipeline.set_source pipeline contents;
              Pipeline.stabilize ();
              stats.st_mtime)
        else
          last_mtime
  in
  watch_loop file pipeline last_mtime

let main () =
  let args = Cli.parse_args () in
  let pipeline = Pipeline.create () in

  (* Attach debug handlers *)
  Pipeline.on_tokens_update pipeline ~f:(fun update ->
      log_stage "tokens" update;
      handle_stage_result ~show:args.Cli.show_lex ~printer:print_tokens update);
  Pipeline.on_program_update pipeline ~f:(fun update ->
      log_stage "program" update;
      handle_stage_result ~show:args.Cli.show_parse ~printer:print_program
        update);
  Pipeline.on_elaborated_update pipeline ~f:(fun update ->
      log_stage "elaborated" update;
      handle_stage_result ~show:args.Cli.show_elab ~printer:print_defs update);

  Pipeline.set_source pipeline (read_file_exn args.input_file);
  Pipeline.stabilize ();
  let initial_mtime =
    match Unix.stat args.input_file with
    | exception Unix.Unix_error _ -> 0.0
    | stats -> stats.st_mtime
  in
  Format.eprintf "[inc] watching %s (poll %.1fs)…@." args.input_file
    poll_seconds;
  watch_loop args.input_file pipeline initial_mtime

let () = main ()
