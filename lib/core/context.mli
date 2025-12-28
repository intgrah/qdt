type entry = {
  name : string option;
  ty : Semantics.vty;
}

type t = {
  entries : entry list;
  env : Semantics.env;
  lvl : int;
}

val empty : t
val bind : string option -> Semantics.vty -> t -> t
val bind_def : string option -> Semantics.vty -> Semantics.vtm -> t -> t
val lookup_idx : t -> Syntax.idx -> Semantics.vty
val lookup_name : t -> string -> (int * Semantics.vty) option
val names : t -> string option list
