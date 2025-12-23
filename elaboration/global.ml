open Syntax
module NameMap = Map.Make (Name)

type inductive_info = {
  ty : ty;
  ctors : (Name.t * ty) list;
}

type rec_rule = {
  rule_ctor_name : Name.t;
  rule_nfields : int;
  rule_rec_args : int list;
  rule_rec_indices : int list list;
}

type recursor_info = {
  ty : vl_ty;
  rec_ind_name : Name.t;
  rec_num_params : int;
  rec_num_indices : int;
  rec_num_motives : int;
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
  ty : vl_ty;
  ind_name : Name.t;
  ctor_idx : int;
}

type entry =
  | Def of {
      ty : vl_ty;
      tm : vl_tm;
    }
  | Opaque of { ty : vl_ty } (* Type formers, e.g. Eq, Nat *)
  | Inductive of inductive_info
  | Structure of {
      ind : inductive_info;
      info : structure_info;
    }
  | Recursor of recursor_info
  | Constructor of constructor_info

type t = entry NameMap.t

let empty : t = NameMap.empty
let find_opt = NameMap.find_opt

let find_tm name env =
  match find_opt name env with
  | Some (Def { tm; _ }) -> Some tm
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
