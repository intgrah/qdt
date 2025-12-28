val check_ty : Global.t -> Context.t -> Frontend.Ast.t -> Syntax.ty

val infer_tm :
  Global.t -> Context.t -> Frontend.Ast.t -> Syntax.tm * Semantics.vty

val check_tm :
  Global.t -> Context.t -> Frontend.Ast.t -> Semantics.vty -> Syntax.tm
