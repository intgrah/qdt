open Syntax
open Frontend

(* Concrete Syntax *)
val pp_cst : Format.formatter -> Cst.t -> unit
val pp_cst_command : Format.formatter -> Cst.Command.t -> unit
val pp_cst_program : Format.formatter -> Cst.program -> unit

(* Abstract Syntax *)
val pp_ast : Format.formatter -> Ast.t -> unit
val pp_ast_command : Format.formatter -> Ast.Command.t -> unit
val pp_ast_program : Format.formatter -> Ast.program -> unit

(* Core Syntax *)
val pp_ty_ctx : string list -> Format.formatter -> ty -> unit
val pp_ty : Format.formatter -> ty -> unit
val pp_tm : Format.formatter -> tm -> unit
val pp_def : Format.formatter -> Name.t * tm * ty -> unit

(* Values *)
val pp_vl_ty : Format.formatter -> vl_ty -> unit
val pp_vl_tm : Format.formatter -> vl_tm -> unit
