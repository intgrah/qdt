open Syntax

let rec quote_tm (l : lvl) (v : tm_val) : tm =
  match v with
  | VLam (Closure_tm (env, body)) ->
      let x_var : tm_val =
        VNeutral { head = HVar l; spine = []; boundary = lazy (Abstract VType) }
      in
      let body_val = Eval.eval_tm (TmVal x_var :: env) body in
      Lam (Type, quote_tm (l + 1) body_val)
  | VNeutral { head; spine; boundary = _ } ->
      let rec quote_spine (t : tm) (sp : spine) : tm =
        match sp with
        | [] -> t
        | FApp (u, _ty) :: rest ->
            let t' = quote_spine t rest in
            App (t', quote_tm l u)
      in
      let head_tm =
        match head with
        | HVar x -> Var (l - x - 1)
        | HMeta m -> Meta m
      in
      quote_spine head_tm spine

let rec quote_ty (l : lvl) (v : ty_val) : ty =
  match v with
  | VPi (a, Closure_ty (env, b)) ->
      let a_ty = quote_ty l a in
      let x_var : tm_val =
        VNeutral { head = HVar l; spine = []; boundary = lazy (Abstract VType) }
      in
      let b_val = Eval.eval_ty (TmVal x_var :: env) b in
      Pi (a_ty, quote_ty (l + 1) b_val)
  | VType -> Type
  | VNeutral { head; spine; boundary = _ } ->
      let quote_spine_ty (t : ty) (sp : spine) : ty =
        match sp with
        | [] -> t
        | _ -> failwith "quote_ty: type-level application not yet supported"
      in
      let head_ty =
        match head with
        | HVar x -> TVar (l - x - 1)
        | HMeta _ ->
            failwith "quote_ty: metavariables in types not yet supported"
      in
      quote_spine_ty head_ty spine

let normalize_tm (env : env) (t : tm) : tm =
  let v = Eval.eval_tm env t in
  quote_tm (List.length env) v

let normalize_ty (env : env) (t : ty) : ty =
  let v = Eval.eval_ty env t in
  quote_ty (List.length env) v
