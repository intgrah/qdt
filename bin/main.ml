let poll_seconds = 0.1

let read_file path =
  try Some (In_channel.with_open_text path In_channel.input_all) with
  | Sys_error msg ->
      Format.eprintf "Failed to read %s: %s@." path msg;
      None

let log_stage stage : 'a Incr.update -> unit = function
  | Initialized _ -> Format.eprintf "[inc] %s@." stage
  | Changed _ -> Format.eprintf "[inc] %s@." stage
  | Invalidated -> Format.eprintf "[inc] %s@." stage

let print_program = Format.printf "%a@." Elaboration.Pretty.pp_ast_program
let print_defs = List.iter (Format.printf "%a@.@." Elaboration.Pretty.pp_def)

let handle_stage_result ~show ~printer : 'a Incr.update -> unit = function
  | Initialized (Ok value)
  | Changed (_, Ok value) ->
      if show then printer value
  | Initialized (Error err)
  | Changed (_, Error err) ->
      Format.printf "%s@." err
  | Invalidated -> ()

let rec watch_loop file pipeline last_mtime =
  Unix.sleepf poll_seconds;
  let last_mtime =
    match Unix.stat file with
    | exception Unix.Unix_error (err, _, _) ->
        Format.eprintf "Error: %s" (Unix.error_message err);
        last_mtime
    | stats ->
        if stats.st_mtime > last_mtime then (
          match read_file file with
          | None -> last_mtime
          | Some contents ->
              Incr.set_source pipeline contents;
              Incr.stabilize ();
              stats.st_mtime
        ) else
          last_mtime
  in
  watch_loop file pipeline last_mtime

let main () =
  let args = Cli.parse_args () in
  let pipeline = Incr.create ~root_dir:args.root_dir () in

  (* Attach debug handlers *)
  Incr.on_program_update pipeline ~f:(fun update ->
      log_stage "program" update;
      handle_stage_result ~show:args.Cli.show_parse ~printer:print_program
        update);
  Incr.on_elaborated_update pipeline ~f:(fun update ->
      log_stage "elaborated" update;
      handle_stage_result ~show:args.Cli.show_elab ~printer:print_defs update);

  Incr.set_source pipeline (Option.get (read_file args.input_file));
  Incr.stabilize ();
  if args.watch then (
    let initial_mtime =
      match Unix.stat args.input_file with
      | exception Unix.Unix_error _ -> 0.0
      | stats -> stats.st_mtime
    in
    Format.eprintf "[inc] watching %s (poll %.1fs)…@." args.input_file
      poll_seconds;
    watch_loop args.input_file pipeline initial_mtime
  )

let () = main ()
