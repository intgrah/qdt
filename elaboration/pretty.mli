open Syntax

(* Raw Syntax *)
val pp_raw : Format.formatter -> Raw.t -> unit
val pp_raw_item : Format.formatter -> Raw.item -> unit
val pp_raw_program : Format.formatter -> Raw.program -> unit

(* Core Syntax *)
val pp_ty_ctx : string list -> Format.formatter -> ty -> unit
val pp_ty : Format.formatter -> ty -> unit
val pp_tm : Format.formatter -> tm -> unit
val ty_to_string : ty -> string
val tm_to_string : tm -> string
val pp_def : Format.formatter -> string list * tm * ty -> unit
