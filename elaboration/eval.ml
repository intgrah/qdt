open Syntax

(* Force value and unfold solved metavariables *)
let rec force : value -> value = function
  | TmVal (VNeutral { head = HMeta id; spine; boundary = _ } as v) -> (
      match lookup_meta id with
      | Solved v' ->
          let v'' =
            match force (TmVal v') with
            | TmVal x -> x
            | TyVal _ -> failwith "force: got ty_val"
          in
          TmVal
            (force_tm
               (List.fold_left
                  (fun acc frame ->
                    match frame with
                    | FApp (u, _ty) -> (
                        match apply (TmVal acc) (TmVal u) with
                        | TmVal tm -> tm
                        | TyVal _ -> failwith "force: got ty_val"))
                  v'' spine))
      | Unsolved -> TmVal v)
  | TmVal v -> TmVal (force_tm v)
  | TyVal v -> TyVal v

and force_tm : tm_val -> tm_val = function
  | VNeutral { head = HMeta id; spine; boundary = _ } as v -> (
      match lookup_meta id with
      | Solved v' ->
          let v'' = force_tm v' in
          force_tm
            (List.fold_left
               (fun acc frame ->
                 match frame with
                 | FApp (u, _ty) -> (
                     match apply (TmVal acc) (TmVal u) with
                     | TmVal tm -> tm
                     | TyVal _ -> failwith "force_tm: got ty_val"))
               v'' spine)
      | Unsolved -> v)
  | v -> v

and apply (t : value) (u : value) : value =
  match (force t, u) with
  | TmVal (VLam clos), TmVal u_val -> TmVal (inst_tm clos (TmVal u_val))
  | TmVal (VNeutral { head; spine; boundary }), TmVal u_val ->
      TmVal
        (VNeutral { head; spine = spine @ [ FApp (u_val, VType) ]; boundary })
  | _ -> failwith "apply"

and inst_tm (Closure_tm (env, body) : tm_closure) (v : value) : tm_val =
  eval_tm (v :: env) body

and inst_ty (Closure_ty (env, body) : ty_closure) (v : value) : ty_val =
  eval_ty (v :: env) body

and eval_tm (env : env) (t : tm) : tm_val =
  match t with
  | Var ix -> (
      match List.nth env ix with
      | TmVal tm_v -> tm_v
      | TyVal _ -> failwith "eval_tm: got ty_val")
  | Lam (_ty, body) -> VLam (Closure_tm (env, body))
  | App (f, a) -> (
      match apply (TmVal (eval_tm env f)) (TmVal (eval_tm env a)) with
      | TmVal tm -> tm
      | TyVal _ -> failwith "eval_tm: got ty_val")
  | Meta id -> (
      match lookup_meta id with
      | Solved v -> force_tm v
      | Unsolved ->
          VNeutral
            { head = HMeta id; spine = []; boundary = lazy (Abstract VType) })

and eval_ty (env : env) : ty -> ty_val = function
  | TVar ix -> (
      match List.nth env ix with
      | TyVal ty_v -> ty_v
      | TmVal tm_v -> (
          match tm_v with
          | VNeutral n ->
              (* TODO this is stupid *)
              VNeutral n
          | _ -> failwith "eval_ty"))
  | Pi (a, b) ->
      let a_val = eval_ty env a in
      VPi (a_val, Closure_ty (env, b))
  | Type -> VType
