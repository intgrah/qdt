type stage_error =
  | Lex_error of string
  | Parse_error of string
  | Elab_error of string

type 'a stage_result = ('a, stage_error) result
type tokens_result = Lexer.token list stage_result
type program_result = Syntax.Raw.program stage_result
type elaborated_result = (Elab.Name.t * Syntax.tm * Syntax.ty) list stage_result

type snapshot = {
  tokens : tokens_result;
  program : program_result;
  elaborated : elaborated_result;
}

type t

module Update : sig
  type 'a t =
    | Initialized of 'a
    | Changed of 'a * 'a
    | Invalidated
end

val pp_stage_error : Format.formatter -> stage_error -> unit
val create : ?root_dir:string -> unit -> t
val set_root_dir : t -> string -> unit
val set_source : t -> string -> unit
val stabilize : unit -> unit
val snapshot : t -> snapshot
val on_tokens_update : t -> f:(tokens_result Update.t -> unit) -> unit
val on_program_update : t -> f:(program_result Update.t -> unit) -> unit
val on_elaborated_update : t -> f:(elaborated_result Update.t -> unit) -> unit
