open Frontend
open Elaboration

type stage_error =
  | Lex_error of string
  | Parse_error of string
  | Elab_error of string

type 'a stage_result = ('a, stage_error) result
type tokens_result = Lexer.token list stage_result
type program_result = Syntax.Raw.program stage_result
type elaborated_result = (Name.t * Syntax.tm * Syntax.ty) list stage_result

type snapshot = {
  tokens : tokens_result;
  program : program_result;
  elaborated : elaborated_result;
}

module Update = struct
  type 'a t =
    | Initialized of 'a
    | Changed of 'a * 'a
    | Invalidated
end

type t = {
  mutable source : string;
  mutable root_dir : string;
  mutable tokens_callback : tokens_result Update.t -> unit;
  mutable program_callback : program_result Update.t -> unit;
  mutable elaborated_callback : elaborated_result Update.t -> unit;
  mutable last_tokens : tokens_result option;
  mutable last_program : program_result option;
  mutable last_elaborated : elaborated_result option;
}

let pp_stage_error fmt = function
  | Lex_error msg -> Format.fprintf fmt "Lexing error: %s" msg
  | Parse_error msg -> Format.fprintf fmt "Parse error: %s" msg
  | Elab_error msg -> Format.fprintf fmt "Elaboration error: %s" msg

let try_lex chars =
  match Lexer.scan [] chars with
  | tokens -> Ok tokens
  | exception Lexer.Illegal_character c ->
      Error (Lex_error (Format.sprintf "Illegal character in input: %c" c))
  | exception Lexer.Unterminated_comment ->
      Error (Lex_error "Unterminated block comment")
  | exception exn -> Error (Lex_error (Printexc.to_string exn))

let try_parse = function
  | Error e -> Error e
  | Ok tokens -> (
      match Parser.parse tokens with
      | program -> Ok program
      | exception Parser.Parse_error msg -> Error (Parse_error msg)
      | exception Parser.Tokens_remaining remaining ->
          Error
            (Parse_error
               (Format.asprintf "Tokens: %a@."
                  (Format.pp_print_list
                     ~pp_sep:(fun fmt () -> Format.fprintf fmt " ")
                     Lexer.pp_token)
                  (List.take 5 remaining)))
      | exception exn -> Error (Parse_error (Printexc.to_string exn)))

let read_file_for_import path =
  In_channel.with_open_text path In_channel.input_all

let parse_for_import source =
  let chars = List.of_seq (String.to_seq source) in
  let tokens = Lexer.scan [] chars in
  Parser.parse tokens

let try_elaborate root_dir = function
  | Error e -> Error e
  | Ok program -> (
      match
        Elab.elab_program_with_imports ~root:root_dir
          ~read_file:read_file_for_import ~parse:parse_for_import program
      with
      | defs -> Ok defs
      | exception Elab.Elab_error msg -> Error (Elab_error msg)
      | exception Elab.Circular_import m ->
          Error
            (Elab_error
               (Format.sprintf "Circular import: %s" (Name.to_string m)))
      | exception Elab.Import_not_found m ->
          Error
            (Elab_error
               (Format.sprintf "Import not found: %s" (Name.to_string m)))
      | exception exn -> Error (Elab_error (Printexc.to_string exn)))

let create ?(root_dir = ".") () =
  {
    source = "";
    root_dir;
    tokens_callback = (fun _ -> ());
    program_callback = (fun _ -> ());
    elaborated_callback = (fun _ -> ());
    last_tokens = None;
    last_program = None;
    last_elaborated = None;
  }

let set_root_dir t dir = t.root_dir <- dir
let set_source t text = t.source <- text

let stabilize_t t =
  let chars = List.of_seq (String.to_seq t.source) in
  let tokens = try_lex chars in
  let program = try_parse tokens in
  let elaborated = try_elaborate t.root_dir program in

  let make_update last new_val =
    match last with
    | None -> Update.Initialized new_val
    | Some old -> Update.Changed (old, new_val)
  in

  t.tokens_callback (make_update t.last_tokens tokens);
  t.program_callback (make_update t.last_program program);
  t.elaborated_callback (make_update t.last_elaborated elaborated);

  t.last_tokens <- Some tokens;
  t.last_program <- Some program;
  t.last_elaborated <- Some elaborated

let current_pipeline : t option ref = ref None

let stabilize () =
  match !current_pipeline with
  | Some t -> stabilize_t t
  | None -> ()

let snapshot t =
  let tokens =
    match t.last_tokens with
    | Some r -> r
    | None -> Error (Lex_error "not initialized")
  in
  let program =
    match t.last_program with
    | Some r -> r
    | None -> Error (Parse_error "not initialized")
  in
  let elaborated =
    match t.last_elaborated with
    | Some r -> r
    | None -> Error (Elab_error "not initialized")
  in
  { tokens; program; elaborated }

let on_tokens_update t ~f =
  t.tokens_callback <- f;
  current_pipeline := Some t

let on_program_update t ~f =
  t.program_callback <- f;
  current_pipeline := Some t

let on_elaborated_update t ~f =
  t.elaborated_callback <- f;
  current_pipeline := Some t
