exception Eval_error of string

val eval_ty : Global.t -> Semantics.env -> Syntax.ty -> Semantics.vty
val do_el : Semantics.vtm -> Semantics.vty
val eval_tm : Global.t -> Semantics.env -> Syntax.tm -> Semantics.vtm
val do_app : Global.t -> Semantics.vtm -> Semantics.vtm -> Semantics.vtm
val conv_ty : Global.t -> int -> Semantics.vty -> Semantics.vty -> bool
