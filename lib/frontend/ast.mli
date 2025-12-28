open Source

type t =
  | Missing of src
  | Ident of src * string
  | App of src * t * t
  | Lam of src * binder * t
  | Pi of src * typed_binder * t
  | Let of src * string * t option * t * t
  | U of src
  | Pair of src * t * t
  | Eq of src * t * t
  | Ann of src * t * t
  | Sorry of src

and binder =
  | Untyped of src * string option
  | Typed of typed_binder

and typed_binder = src * string option * t

module Command : sig
  type import = {
    src : src;
    module_name : string;
  }

  type definition = {
    src : src;
    name : string;
    params : typed_binder list;
    ty_opt : t option;
    body : t;
  }

  type example = {
    src : src;
    params : typed_binder list;
    ty_opt : t option;
    body : t;
  }

  type axiom = {
    src : src;
    name : string;
    params : typed_binder list;
    ty : t;
  }

  type inductive_constructor = {
    src : src;
    name : string;
    params : typed_binder list;
    ty_opt : t option;
  }

  type inductive = {
    src : src;
    name : string;
    params : typed_binder list;
    ty_opt : t option;
    ctors : inductive_constructor list;
  }

  type structure_field = {
    src : src;
    name : string;
    params : typed_binder list;
    ty : t;
  }

  type structure = {
    src : src;
    name : string;
    params : typed_binder list;
    ty_opt : t option;
    fields : structure_field list;
  }

  type t =
    | Import of import
    | Definition of definition
    | Example of example
    | Axiom of axiom
    | Inductive of inductive
    | Structure of structure
end

type program = Command.t list

val get_src : t -> src
