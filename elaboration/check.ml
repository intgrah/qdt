open Syntax

type context = {
  env : env;
  lvl : lvl;
  types : ty_val list;
}

let empty_context : context = { env = []; lvl = 0; types = [] }

let bind_var (ctx : context) (ty : ty_val) : context =
  let var : tm_val =
    VNeutral { head = HVar ctx.lvl; spine = []; boundary = lazy (Abstract ty) }
  in
  { env = TmVal var :: ctx.env; lvl = ctx.lvl + 1; types = ty :: ctx.types }

let rec check (ctx : context) (t : tm) (ty : ty_val) : tm =
  match (t, ty) with
  (* λx.t : Π A. B *)
  | Lam (_ann_ty, body), VPi (a, Closure_ty (_, b_ty)) ->
      let ctx' = bind_var ctx a in
      let x_var : tm_val =
        VNeutral
          { head = HVar ctx.lvl; spine = []; boundary = lazy (Abstract a) }
      in
      let b_val = Eval.eval_ty (TmVal x_var :: ctx.env) b_ty in
      let body_checked = check ctx' body b_val in
      let a_ty = Quote.quote_ty ctx.lvl a in
      Lam (a_ty, body_checked)
  (* Switch to infer mode *)
  | _ -> (
      let t', inferred_ty = infer ctx t in
      try
        Unify.unify_ty ctx.lvl inferred_ty ty;
        t'
      with
      | Unify.Unify_error ->
          failwith (Format.sprintf "Type mismatch at level %d" ctx.lvl))

and infer (ctx : context) (t : tm) : tm * ty_val =
  match t with
  | Var ix ->
      let ty = List.nth ctx.types ix in
      (Var ix, ty)
  (* TODO not need annotation *)
  | Lam (ann_ty, body) ->
      let a_val = Eval.eval_ty ctx.env ann_ty in
      let ctx' = bind_var ctx a_val in
      let body', b_ty = infer ctx' body in
      let b_ty_quoted = Quote.quote_ty (ctx.lvl + 1) b_ty in
      (Lam (ann_ty, body'), VPi (a_val, Closure_ty (ctx.env, b_ty_quoted)))
  | App (f, a) -> (
      let f', f_ty = infer ctx f in
      match Eval.force (TyVal f_ty) with
      | TyVal (VPi (a_ty, Closure_ty (env, b_ty))) ->
          let a_checked = check ctx a a_ty in
          let a_val = Eval.eval_tm ctx.env a_checked in
          let b_val = Eval.eval_ty (TmVal a_val :: env) b_ty in
          (App (f', a_checked), b_val)
      | _ -> failwith "Application of non-function type")
  | Meta m -> (
      match lookup_meta m with
      | Solved v ->
          let t = Quote.quote_tm ctx.lvl v in
          infer ctx t
      | Unsolved -> (Meta m, VType))

let rec infer_ty (ctx : context) (t : ty) : ty * ty_val =
  match t with
  | TVar ix ->
      let ty = List.nth ctx.types ix in
      (TVar ix, ty)
  | Pi (a, b) ->
      let a', _a_ty = infer_ty ctx a in
      let a_val = Eval.eval_ty ctx.env a' in
      let ctx' = bind_var ctx a_val in
      let b', _b_ty = infer_ty ctx' b in
      (Pi (a', b'), VType)
  | Type -> (Type, VType)
