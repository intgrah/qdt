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

type constructor_info = {
  ty : Syntax.ty; (* (A : Type) -> Vector A 0 *)
  ctor_name : Name.t; (* ["Vector"; "nil"] *)
}

type inductive_info = {
  ty : ty; (* Type -> Nat -> Type *)
  ind_ctors : constructor_info list; (* nil, cons *)
}

type rec_rule = {
  rule_ctor_name : Name.t; (* ["Vector"; "cons"] *)
  rule_nfields : int; (* 3 (n, head, tail) *)
  rule_rec_rhs : tm;
      (* cons_case n head tail (Vector.rec A nil_case cons_case tail)  *)
}

type recursor_info = {
  ty : ty;
      (* (A : Type) ->
         (motive : (n : Nat) -> Vector A n -> Type) ->
         (nil_case : motive 0 (Vector.nil A)) ->
         (cons_case :
           (k : Nat) ->
           (head : A) ->
           (tail : Vector A k) ->
           (ih_tail : motive k tail) ->
           motive (Nat.succ k) (Vector.cons A k head tail)
         (m : Nat) ->
         (major : Vector A m) ->
         motive m major
         ) *)
  rec_name : Name.t; (* ["Vector"; "rec"] *)
  rec_num_params : int; (* 1 (A) *)
  rec_num_indices : int; (* 1 (n) *)
  rec_rules : rec_rule list; (* nil_case, cons_case *)
}

type structure_info = {
  ty : ty; (* Type -> Type -> Type *)
  struct_ind_name : Name.t; (* ["Prod"] *)
  struct_ctor_name : Name.t; (* ["Prod"; "mk"] *)
  struct_num_params : int; (* 2 (A, B) *)
  struct_fields : string list; (* ["fst", "snd"] *)
}

type entry =
  | Definition of {
      ty : ty;
      tm : tm;
    }
  | Opaque of { ty : ty } (* Type formers, e.g. Eq, Nat *)
  | Axiom of { ty : ty }
  | Inductive of inductive_info
  | Structure of structure_info
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
  | Some (Structure info) -> Some { ty = info.ty; ind_ctors = [] }
  | _ -> None

let find_structure name env =
  match find_opt name env with
  | Some (Structure info) -> Some info
  | _ -> None

let find_ty name env : ty option =
  match find_opt name env with
  | Some (Definition { ty; _ })
  | Some (Opaque { ty })
  | Some (Axiom { ty })
  | Some (Recursor { ty; _ })
  | Some (Constructor { ty; _ })
  | Some (Inductive { ty; _ })
  | Some (Structure { ty; _ }) ->
      Some ty
  | None -> None
