val elab_params_from :
  Context.t ->
  Global.t ->
  Frontend.Ast.typed_binder list ->
  Context.t * (string option * Syntax.ty) list

val elab_params :
  Global.t ->
  Frontend.Ast.typed_binder list ->
  Context.t * (string option * Syntax.ty) list
