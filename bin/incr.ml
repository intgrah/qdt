open Frontend
open Elaboration

type 'a stage_result = ('a, string) result
type program_result = Ast.program stage_result
type elaborated_result = (Name.t * Syntax.tm * Syntax.ty) list stage_result

type snapshot = {
  program : program_result;
  elaborated : elaborated_result;
}

type 'a update =
  | Initialized of 'a
  | Changed of 'a * 'a
  | Invalidated

type t = {
  mutable source : string;
  mutable root_dir : string;
  mutable program_callback : program_result update -> unit;
  mutable elaborated_callback : elaborated_result update -> unit;
  mutable last_program : program_result option;
  mutable last_elaborated : elaborated_result option;
}

let try_parse source =
  match Parser.parse source with
  | program -> Ok program
  | exception Parser.Syntax_error { msg; pos } ->
      let msg =
        Format.asprintf "Parse error: %s (at line %d, col %d)" msg pos.line
          pos.column
      in
      Error msg
  | exception exn ->
      Error (Format.asprintf "Parse error: %s" (Printexc.to_string exn))

let read_file_for_import path =
  In_channel.with_open_text path In_channel.input_all

let try_elaborate root_dir = function
  | Error e -> Error e
  | Ok program -> (
      match
        Elab.elab_program_with_imports ~root:root_dir
          ~read_file:read_file_for_import program
      with
      | defs -> Ok defs
      | exception Error.Error err ->
          Error
            (Format.asprintf "Elaboration error: %s"
               (Error.to_string ~filename:"<unknown>" err))
      | exception Parser.Syntax_error { Parser.msg; _ } ->
          Error (Format.asprintf "Parse error: %s" msg)
      | exception exn ->
          Error
            (Format.asprintf "Elaboration error: %s" (Printexc.to_string exn)))

let create ?(root_dir = ".") () =
  {
    source = "";
    root_dir;
    program_callback = (fun _ -> ());
    elaborated_callback = (fun _ -> ());
    last_program = None;
    last_elaborated = None;
  }

let set_root_dir t dir = t.root_dir <- dir
let set_source t text = t.source <- text

let stabilize_t t =
  let cst_program = try_parse t.source in
  let program =
    match cst_program with
    | Ok cst -> Ok (Desugar.desugar_program cst)
    | Error e -> Error e
  in
  let elaborated = try_elaborate t.root_dir program in

  let make_update last new_val =
    match last with
    | None -> Initialized new_val
    | Some old -> Changed (old, new_val)
  in

  t.program_callback (make_update t.last_program program);
  t.elaborated_callback (make_update t.last_elaborated elaborated);

  t.last_program <- Some program;
  t.last_elaborated <- Some elaborated

let current_pipeline : t option ref = ref None

let stabilize () =
  match !current_pipeline with
  | Some t -> stabilize_t t
  | None -> ()

let snapshot t =
  let program =
    match t.last_program with
    | Some r -> r
    | None -> Error "not initialized"
  in
  let elaborated =
    match t.last_elaborated with
    | Some r -> r
    | None -> Error "not initialized"
  in
  { program; elaborated }

let on_program_update t ~f =
  t.program_callback <- f;
  current_pipeline := Some t

let on_elaborated_update t ~f =
  t.elaborated_callback <- f;
  current_pipeline := Some t
