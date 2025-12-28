open Syntax

module NameMap : sig
  type 'a t

  val empty : 'a t
  val add : Name.t -> 'a -> 'a t -> 'a t
  val cardinal : 'a t -> int
  val find_opt : Name.t -> 'a t -> 'a option
end =
  Map.Make (Name)

include NameMap

type inductive_info = {
  ty : ty;
  ctors : (Name.t * ty) list;
}

type rec_rule = {
  rule_ctor_name : Name.t;
  rule_nfields : int;
  rule_rec_rhs : tm; (* Has free variables *)
}

type recursor_info = {
  ty : ty;
  rec_ind_name : Name.t;
  rec_num_params : int;
  rec_num_indices : int;
  rec_num_methods : int;
  rec_rules : rec_rule list;
}

type structure_info = {
  struct_ind_name : Name.t;
  struct_ctor_name : Name.t;
  struct_num_params : int;
  struct_num_fields : int;
  struct_field_names : string list;
}

type constructor_info = {
  ty : ty;
  ind_name : Name.t;
  ctor_idx : int;
}

type entry =
  | Definition of {
      ty : ty;
      tm : tm;
    }
  | Opaque of { ty : ty } (* Type formers, e.g. Eq, Nat *)
  | Axiom of { ty : ty }
  | Inductive of inductive_info
  | Structure of {
      ind : inductive_info;
      info : structure_info;
    }
  | Recursor of recursor_info
  | Constructor of constructor_info

type t = entry NameMap.t

let find_definition name env =
  match find_opt name env with
  | Some (Definition { tm; _ }) -> Some tm
  | _ -> None

let find_recursor name env =
  match find_opt name env with
  | Some (Recursor info) -> Some info
  | _ -> None

let find_constructor name env =
  match find_opt name env with
  | Some (Constructor info) -> Some info
  | _ -> None

let find_inductive name env =
  match find_opt name env with
  | Some (Inductive info) -> Some info
  | Some (Structure { ind; _ }) -> Some ind
  | _ -> None

let find_structure name env =
  match find_opt name env with
  | Some (Structure { info; _ }) -> Some info
  | _ -> None

let find_ty name env : ty option =
  match find_opt name env with
  | Some (Definition { ty; _ })
  | Some (Opaque { ty })
  | Some (Axiom { ty })
  | Some (Recursor { ty; _ })
  | Some (Constructor { ty; _ }) ->
      Some ty
  | Some (Inductive { ty; _ }) -> Some ty
  | Some (Structure { ind = { ty; _ }; _ }) -> Some ty
  | None -> None
