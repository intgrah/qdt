open Frontend
open Syntax

(* Raw Syntax *)
val pp_raw : Format.formatter -> Raw_syntax.t -> unit
val pp_raw_item : Format.formatter -> Raw_syntax.item -> unit
val pp_raw_program : Format.formatter -> Raw_syntax.program -> unit

(* Core Syntax *)
val pp_ty_ctx : string list -> Format.formatter -> ty -> unit
val pp_ty : Format.formatter -> ty -> unit
val pp_tm : Format.formatter -> tm -> unit
val pp_def : Format.formatter -> Name.t * tm * ty -> unit

(* Values *)
val pp_vl_ty : Format.formatter -> vl_ty -> unit
val pp_vl_tm : Format.formatter -> vl_tm -> unit
