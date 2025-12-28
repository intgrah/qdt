open Core

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
      handle_stage_result ~show:args.Cli.show_parse
        ~printer:(Format.printf "%a@." Pretty.pp_ast_program)
        update);
  Incr.on_elaborated_update pipeline ~f:(fun update ->
      log_stage "elaborated" update;
      let show = args.Cli.show_elab <> [] in
      handle_stage_result ~show
        ~printer:(fun genv ->
          let print_entry (name : Name.t) (entry : Global.entry) =
            match Global.find_ty name genv with
            | None -> ()
            | Some ty -> (
                match entry with
                | Global.Definition { tm; _ } ->
                    Format.printf "%a@.@." Pretty.pp_def (name, tm, ty)
                | Global.Opaque _ ->
                    Format.printf "@[<hov 2>opaque %a :@;<1 4>%a@]@.@." Name.pp
                      name Pretty.pp_ty ty
                | Global.Axiom _ ->
                    Format.printf "@[<hov 2>axiom %a :@;<1 4>%a@]@.@." Name.pp
                      name Pretty.pp_ty ty
                | Global.Inductive _ ->
                    Format.printf "@[<hov 2>inductive %a :@;<1 4>%a@]@.@."
                      Name.pp name Pretty.pp_ty ty
                | Global.Structure _ ->
                    Format.printf "@[<hov 2>structure %a :@;<1 4>%a@]@.@."
                      Name.pp name Pretty.pp_ty ty
                | Global.Recursor _ ->
                    Format.printf "@[<hov 2>opaque %a :@;<1 4>%a@]@.@." Name.pp
                      name Pretty.pp_ty ty
                | Global.Constructor _ ->
                    Format.printf "@[<hov 2>opaque %a :@;<1 4>%a@]@.@." Name.pp
                      name Pretty.pp_ty ty)
          in
          List.iter
            (fun name_str ->
              let name = Name.parse name_str in
              match Global.find_opt name genv with
              | None -> Format.printf "Unknown constant: %s@." name_str
              | Some entry -> print_entry name entry)
            args.show_elab)
        update);

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
