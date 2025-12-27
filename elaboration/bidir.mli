val check_ty : Global.t -> Context.t -> Frontend.Ast.t -> Syntax.ty

val infer_tm :
  Global.t -> Context.t -> Frontend.Ast.t -> Syntax.tm * Syntax.vl_ty

val check_tm :
  Global.t -> Context.t -> Frontend.Ast.t -> Syntax.vl_ty -> Syntax.tm
