val desugar_sigma :
  Raw_syntax.typed_binder_group -> Raw_syntax.t -> Raw_syntax.t

val desugar_prod : Raw_syntax.t -> Raw_syntax.t -> Raw_syntax.t
val desugar_nat_lit : int -> Raw_syntax.t
val desugar_add : Raw_syntax.t -> Raw_syntax.t -> Raw_syntax.t
val desugar_sub : Raw_syntax.t -> Raw_syntax.t -> Raw_syntax.t
