open Syntax

type t =
  | Missing of src
  | Ident of src * string (* x *)
  | App of src * t * t (* a b *)
  | Lam of src * binder_group list * t (* fun x y : T => e *)
  | Pi of src * typed_binder_group * t (* (x y : A) → B *)
  | Arrow of src * t * t (* A → B *)
  | Let of src * string * t option * t * t (* let x : A := a; b *)
  | U of src (* Type *)
  | Sigma of src * typed_binder_group * t (* (x y : A) × B *)
  | Prod of src * t * t (* A × B *)
  | Pair of src * t * t (* (a, b) *)
  | Eq of src * t * t (* a = b, desugars to Eq _ a b *)
  | NatLit of src * int (* 0 *)
  | Add of src * t * t (* a + b *)
  | Sub of src * t * t (* a - b *)
  | Mul of src * t * t (* a * b *)
  | Ann of src * t * t (* (a : A) *)
  | Sorry of src (* sorry *)

and binder_group =
  | Untyped of src * string option (* x *)
  | Typed of typed_binder_group (* (x y : A) *)

and typed_binder_group = src * string option list * t (* (x y : A) *)

module Command = struct
  type import = {
    src : src;
    module_name : string;
  }

  type definition = {
    src : src;
    name : string;
    params : typed_binder_group list;
    ty_opt : t option;
    body : t;
  }

  type example = {
    src : src;
    params : typed_binder_group list;
    ty_opt : t option;
    body : t;
  }

  type axiom = {
    src : src;
    name : string;
    params : typed_binder_group list;
    ty : t;
  }

  type inductive_constructor = {
    src : src;
    name : string;
    params : typed_binder_group list;
    ty_opt : t option;
  }

  type inductive = {
    src : src;
    name : string;
    params : typed_binder_group list;
    ty_opt : t option;
    ctors : inductive_constructor list;
  }

  type structure_field = {
    src : src;
    name : string;
    params : typed_binder_group list;
    ty : t;
  }

  type structure = {
    src : src;
    name : string;
    params : typed_binder_group list;
    ty_opt : t option;
    fields : structure_field list;
  }

  type t =
    | Import of import
    | Definition of definition (* def x : A := b *)
    | Example of example (* example (x y : A) : B *)
    | Axiom of axiom (* axiom x : A *)
    | Inductive of inductive (* inductive A : T where *)
    | Structure of structure (* structure A : T where *)
end

type program = Command.t list
