exception Elab_error of string

val elab_program :
  Lang.Raw_syntax.program -> (string * Syntax.tm * Syntax.val_ty) list

val check :
  Check.context ->
  string list ->
  Lang.Raw_syntax.t ->
  Syntax.val_ty ->
  Syntax.tm

val infer :
  Check.context -> string list -> Lang.Raw_syntax.t -> Syntax.tm * Syntax.val_ty
