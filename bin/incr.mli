open Frontend
open Core

type 'a stage_result = ('a, string) result
type program_result = Ast.program stage_result
type elaborated_result = Global.t stage_result

type snapshot = {
  program : program_result;
  elaborated : elaborated_result;
}

type t

type 'a update =
  | Initialized of 'a
  | Changed of 'a * 'a
  | Invalidated

val create : ?root_dir:string -> unit -> t
val set_root_dir : t -> string -> unit
val set_source : t -> string -> unit
val stabilize : unit -> unit
val snapshot : t -> snapshot
val on_program_update : t -> f:(program_result update -> unit) -> unit
val on_elaborated_update : t -> f:(elaborated_result update -> unit) -> unit
