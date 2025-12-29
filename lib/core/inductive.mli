val elab_inductive : Global.t -> Frontend.Ast.Command.inductive -> Global.t

val declare_inductive :
  Global.t ->
  Name.t ->
  (string option * Syntax.ty) list ->
  Syntax.ty ->
  (Name.t * Syntax.ty) list ->
  Global.t

val is_recursive_arg_ty : Name.t -> Syntax.ty -> bool
