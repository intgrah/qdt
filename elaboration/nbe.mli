exception Eval_error of string

val eval_ty : Global.t -> Syntax.env -> Syntax.ty -> Syntax.vl_ty
val do_el : Syntax.vl_tm -> Syntax.vl_ty
val eval_tm : Global.t -> Syntax.env -> Syntax.tm -> Syntax.vl_tm
val do_app : Global.t -> Syntax.vl_tm -> Syntax.vl_tm -> Syntax.vl_tm
val conv_ty : Global.t -> int -> Syntax.vl_ty -> Syntax.vl_ty -> bool
val conv_tm : Global.t -> int -> Syntax.vl_tm -> Syntax.vl_tm -> bool
