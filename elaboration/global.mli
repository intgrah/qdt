type t

type constructor_info = {
  ty : Syntax.ty;
  ctor_name : Name.t;
}

type inductive_info = {
  ty : Syntax.ty;
  ind_ctors : constructor_info list;
}

type rec_rule = {
  rule_ctor_name : Name.t;
  rule_nfields : int;
  rule_rec_rhs : Syntax.tm;
}

type recursor_info = {
  ty : Syntax.ty;
  rec_name : Name.t;
  rec_num_params : int;
  rec_num_indices : int;
  rec_rules : rec_rule list;
}

type structure_info = {
  ty : Syntax.ty;
  struct_ind_name : Name.t;
  struct_ctor_name : Name.t;
  struct_num_params : int;
  struct_fields : string list;
}

type entry =
  | Definition of {
      ty : Syntax.ty;
      tm : Syntax.tm;
    }
  | Opaque of { ty : Syntax.ty }
  | Axiom of { ty : Syntax.ty }
  | Inductive of inductive_info
  | Structure of structure_info
  | Recursor of recursor_info
  | Constructor of constructor_info

val empty : t
val add : Name.t -> entry -> t -> t
val cardinal : t -> int
val find_opt : Name.t -> t -> entry option
val find_definition : Name.t -> t -> Syntax.tm option
val find_recursor : Name.t -> t -> recursor_info option
val find_constructor : Name.t -> t -> constructor_info option
val find_inductive : Name.t -> t -> inductive_info option
val find_structure : Name.t -> t -> structure_info option
val find_ty : Name.t -> t -> Syntax.ty option
