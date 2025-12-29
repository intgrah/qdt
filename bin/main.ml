open Frontend
open Core

let read_file path =
  try Some (In_channel.with_open_text path In_channel.input_all) with
  | Sys_error msg ->
      Format.eprintf "Failed to read %s: %s@." path msg;
      None

let read_file_exn path = In_channel.with_open_text path In_channel.input_all

let parse source =
  match Parser.parse source with
  | cst -> Ok (Desugar.desugar_program cst)
  | exception Parser.Syntax_error { msg; pos } ->
      Error
        (Format.asprintf "Parse error: %s (at line %d, col %d)" msg pos.line
           pos.column)
  | exception exn ->
      Error (Format.asprintf "Parse error: %s" (Printexc.to_string exn))

let elaborate ~current_file program =
  match program with
  | Error e -> Error e
  | Ok prog -> (
      match
        Elab.elab_program_with_imports ~current_file ~read_file:read_file_exn
          prog
      with
      | Ok defs -> Ok defs
      | Error _defs -> Error ""
      | exception Parser.Syntax_error { Parser.msg; _ } ->
          Error (Format.asprintf "Parse error in import: %s" msg)
      | exception exn ->
          Error (Format.asprintf "Error: %s" (Printexc.to_string exn)))

let print_entry genv (name : Name.t) (entry : Global.entry) =
  match Global.find_ty name genv with
  | None -> ()
  | Some ty -> (
      match entry with
      | Global.Definition { tm; _ } ->
          Format.printf "%a@.@." Pretty.pp_def (name, tm, ty)
      | _ ->
          Format.printf "@[<hov 2>%a :@;<1 4>%a@]@.@." Name.pp name Pretty.pp_ty
            ty)

let run_once (args : Cli.options) =
  match read_file args.input_file with
  | None -> exit 1
  | Some source -> (
      let program = parse source in
      let elaborated = elaborate ~current_file:args.input_file program in
      (if args.show_parse then
         match program with
         | Ok prog -> Format.printf "%a@." Pretty.pp_ast_program prog
         | Error _ -> ());
      (match elaborated with
      | Ok genv ->
          List.iter
            (fun name_str ->
              let name = Name.parse name_str in
              match Global.find_opt name genv with
              | None -> Format.printf "Unknown constant: %s@." name_str
              | Some entry -> print_entry genv name entry)
            args.show_elab
      | Error msg -> if msg <> "" then Format.eprintf "%s@." msg);
      match elaborated with
      | Error _ -> exit 1
      | Ok _ -> ())

let poll_seconds = 0.1

let rec watch_loop (args : Cli.options) last_mtime =
  Unix.sleepf poll_seconds;
  let last_mtime =
    match Unix.stat args.input_file with
    | exception Unix.Unix_error (err, _, _) ->
        Format.eprintf "Error: %s@." (Unix.error_message err);
        last_mtime
    | stats ->
        if stats.st_mtime > last_mtime then (
          run_once args;
          stats.st_mtime
        ) else
          last_mtime
  in
  watch_loop args last_mtime

let main () =
  let args = Cli.parse_args () in
  run_once args;
  if args.watch then (
    let initial_mtime =
      match Unix.stat args.input_file with
      | exception Unix.Unix_error _ -> 0.0
      | stats -> stats.st_mtime
    in
    Format.eprintf "[watch] %s (poll %.1fs)@." args.input_file poll_seconds;
    watch_loop args initial_mtime
  )

let () = main ()
