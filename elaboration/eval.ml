open Syntax

let rec eval (env : env) : tm -> vl = function
  | Var ix -> List.nth env ix
  | Global name -> (
      match lookup_global name with
      | Some { value; _ } -> value
      | None -> failwith ("Undefined global: " ^ name))
  | Lam (x, t) -> VLam (x, Closure (env, t))
  | App (t, u) -> apply_frame (eval env t) (FApp (eval env u))
  | U -> VU
  | Pi (x, a, b) -> VPi (x, eval env a, Closure (env, b))
  | Let (_, _, t, u) -> eval (eval env t :: env) u
  | Meta m -> meta m
  | InsertedMeta (m, bds) -> apply_bound env (meta m) bds
  | Unit -> VUnit
  | UnitTerm -> VUnitTerm
  | Prod (a, b) -> VProd (eval env a, eval env b)
  | Pair (t, u) -> VPair (eval env t, eval env u)
  | Fst t -> apply_frame (eval env t) FFst
  | Snd t -> apply_frame (eval env t) FSnd

and ( $$ ) (Closure (env, t) : closure) (u : vl) : vl = eval (u :: env) t

and apply_frame (t : vl) (fr : frame) : vl =
  match (t, fr) with
  | VLam (_, clos), FApp u -> clos $$ u
  | VPair (a, _), FFst -> a
  | VPair (_, b), FSnd -> b
  | VFlex (m, sp), _ -> VFlex (m, sp @ [ fr ])
  | VRigid (x, sp), _ -> VRigid (x, sp @ [ fr ])
  | _ -> failwith "apply_frame: stuck"

and apply_spine (t : vl) (sp : spine) : vl = List.fold_left apply_frame t sp

and apply_bound (env : env) (v : vl) (bds : bd list) : vl =
  match (env, bds) with
  | [], [] -> v
  | t :: env', Bound :: bds' -> apply_frame (apply_bound env' v bds') (FApp t)
  | _ :: env', Defined :: bds' -> apply_bound env' v bds'
  | _ -> failwith "apply_bound: mismatched env and bds"

and meta (m : meta_id) : vl =
  match lookup_meta m with
  | Some v -> v
  | None -> VFlex (m, [])

let rec force : vl -> vl = function
  | VFlex (m, sp) -> (
      match lookup_meta m with
      | Some t -> force (apply_spine t sp)
      | None -> VFlex (m, sp))
  | v -> v
