open Syntax

let rec eval (env : env) : tm -> val_ty = function
  | Var ix -> List.nth env ix
  | Lam (x, t) -> VLam (x, Closure (env, t))
  | App (t, u) -> apply_ty (eval env t) (eval env u)
  | U -> VU
  | Pi (x, a, b) -> VPi (x, eval env a, Closure (env, b))
  | Let (_, _, t, u) -> eval (eval env t :: env) u
  | Meta m -> meta m
  | InsertedMeta (m, bds) -> apply_bound env (meta m) bds

and ( $$ ) (Closure (env, t) : closure) (u : val_ty) : val_ty =
  eval (u :: env) t

and apply_ty (t : val_ty) (u : val_ty) : val_ty =
  match t with
  | VLam (_, clos) -> clos $$ u
  | VFlex (m, sp) -> VFlex (m, sp @ [ u ])
  | VRigid (x, sp) -> VRigid (x, sp @ [ u ])
  | _ -> failwith "apply_ty: impossible"

and apply_spine (t : val_ty) (sp : spine) : val_ty =
  List.fold_left apply_ty t sp

and apply_bound (env : env) (v : val_ty) (bds : bd list) : val_ty =
  match (env, bds) with
  | [], [] -> v
  | t :: env', Bound :: bds' -> apply_ty (apply_bound env' v bds') t
  | _ :: env', Defined :: bds' -> apply_bound env' v bds'
  | _ -> failwith "apply_bound: mismatched env and bds"

and meta (m : meta_id) : val_ty =
  match lookup_meta m with
  | Some v -> v
  | None -> VFlex (m, [])

let rec force : val_ty -> val_ty = function
  | VFlex (m, sp) -> (
      match lookup_meta m with
      | Some t -> force (apply_spine t sp)
      | None -> VFlex (m, sp))
  | v -> v
