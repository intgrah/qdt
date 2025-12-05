open Syntax

(* Raw Syntax *)
val pp_raw : Format.formatter -> raw -> unit
val pp_raw_item : Format.formatter -> raw_item -> unit
val pp_raw_program : Format.formatter -> raw_program -> unit

(* Core Syntax *)
val pp_ty_ctx : string list -> Format.formatter -> ty -> unit
val pp_ty : Format.formatter -> ty -> unit
val pp_tm : Format.formatter -> tm -> unit
val ty_to_string : ty -> string
val tm_to_string : tm -> string
val pp_def : Format.formatter -> string * tm * ty -> unit
