exception Elab_error of string

val elab_program :
  Lang.Raw_syntax.program -> (string * Syntax.tm * Syntax.vl) list

val check :
  Check.context -> string list -> Lang.Raw_syntax.t -> Syntax.vl -> Syntax.tm

val infer :
  Check.context -> string list -> Lang.Raw_syntax.t -> Syntax.tm * Syntax.vl
