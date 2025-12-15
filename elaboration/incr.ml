module Inc = Incremental.Make ()

type stage_error =
  | Lex_error of string
  | Parse_error of string
  | Elab_error of string

type 'a stage_result = ('a, stage_error) result
type tokens_result = Lexer.token list stage_result
type program_result = Syntax.Raw.program stage_result
type elaborated_result = (string * Syntax.tm * Syntax.ty) list stage_result

type snapshot = {
  tokens : tokens_result;
  program : program_result;
  elaborated : elaborated_result;
}

type t = {
  source : string Inc.Var.t;
  tokens_obs : tokens_result Inc.Observer.t;
  program_obs : program_result Inc.Observer.t;
  elaborated_obs : elaborated_result Inc.Observer.t;
}

module Update : sig
  type 'a t = 'a Inc.Observer.Update.t =
    | Initialized of 'a
    | Changed of 'a * 'a
    | Invalidated
end =
  Inc.Observer.Update

let pp_stage_error fmt = function
  | Lex_error msg -> Format.fprintf fmt "Lexing error: %s" msg
  | Parse_error msg -> Format.fprintf fmt "Parse error: %s" msg
  | Elab_error msg -> Format.fprintf fmt "Elaboration error: %s" msg

let summarize_tokens tokens =
  let buf = Buffer.create 128 in
  let fmt = Format.formatter_of_buffer buf in
  let rec loop idx = function
    | [] -> ()
    | tok :: rest ->
        if idx < 5 then (
          if idx > 0 then
            Format.fprintf fmt " ";
          Lexer.pp_token fmt tok;
          loop (idx + 1) rest)
  in
  loop 0 tokens;
  Format.pp_print_flush fmt ();
  let summary = Buffer.contents buf in
  let truncated = List.length tokens > 5 in
  Format.sprintf "Unexpected tokens remaining: %s%s" summary
    (if truncated then
       "..."
     else
       "")

let try_lex chars =
  match Lexer.scan [] chars with
  | tokens -> Ok tokens
  | exception Lexer.Illegal_character ->
      Error (Lex_error "Illegal character in input")
  | exception Lexer.Unterminated_comment ->
      Error (Lex_error "Unterminated block comment")
  | exception exn -> Error (Lex_error (Printexc.to_string exn))

let try_parse = function
  | Error _ as err -> err
  | Ok tokens -> (
      match Parser.parse tokens with
      | program -> Ok program
      | exception Parser.Parse_error msg -> Error (Parse_error msg)
      | exception Parser.Tokens_remaining remaining ->
          Error (Parse_error (summarize_tokens remaining))
      | exception exn -> Error (Parse_error (Printexc.to_string exn)))

let try_elaborate = function
  | Error e -> Error e
  | Ok program -> (
      match Elab.elab_program program with
      | defs -> Ok defs
      | exception Elab.Elab_error msg -> Error (Elab_error msg)
      | exception exn -> Error (Elab_error (Printexc.to_string exn)))

let create () =
  let source = Inc.Var.create "" in
  let chars =
    Inc.map (Inc.Var.watch source) ~f:(fun text ->
        List.of_seq (String.to_seq text))
  in
  let tokens = Inc.map chars ~f:try_lex in
  Inc.set_cutoff tokens (Inc.Cutoff.of_equal ( = ));
  let program = Inc.map tokens ~f:try_parse in
  Inc.set_cutoff program (Inc.Cutoff.of_equal ( = ));
  let elaborated = Inc.map program ~f:try_elaborate in
  Inc.set_cutoff elaborated (Inc.Cutoff.of_equal ( = ));
  let tokens_obs = Inc.observe tokens in
  let program_obs = Inc.observe program in
  let elaborated_obs = Inc.observe elaborated in
  { source; tokens_obs; program_obs; elaborated_obs }

let set_source t text = Inc.Var.set t.source text
let stabilize () = Inc.stabilize ()

let snapshot t =
  {
    tokens = Inc.Observer.value_exn t.tokens_obs;
    program = Inc.Observer.value_exn t.program_obs;
    elaborated = Inc.Observer.value_exn t.elaborated_obs;
  }

let on_tokens_update t ~f = Inc.Observer.on_update_exn t.tokens_obs ~f
let on_program_update t ~f = Inc.Observer.on_update_exn t.program_obs ~f
let on_elaborated_update t ~f = Inc.Observer.on_update_exn t.elaborated_obs ~f
