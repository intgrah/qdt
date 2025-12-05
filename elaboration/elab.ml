open Syntax

exception Elab_error of string

(* ========== Evaluation ========== *)

let rec eval_ty (env : env) : ty -> vl_ty = function
  | TyU -> VTyU
  | TyPi (x, a, b) -> VTyPi (x, eval_ty env a, ClosTy (env, b))
  | TySigma (x, a, b) -> VTySigma (x, eval_ty env a, ClosTy (env, b))
  | TyUnit -> VTyUnit
  | TyEmpty -> VTyEmpty
  | TyInt -> VTyInt
  | TyEq (e1, e2, a) -> VTyEq (eval_tm env e1, eval_tm env e2, eval_ty env a)
  | TyEl t -> do_el env (eval_tm env t)

and do_el (env : env) : vl_tm -> vl_ty = function
  | VTmPiHat (x, a, ClosTm (env', b)) ->
      VTyPi (x, do_el env a, ClosTy (env', TyEl b))
  | VTmSigmaHat (x, a, ClosTm (env', b)) ->
      VTySigma (x, do_el env a, ClosTy (env', TyEl b))
  | VTmUnitHat -> VTyUnit
  | VTmEmptyHat -> VTyEmpty
  | VTmIntHat -> VTyInt
  | VTmEqHat (a, t, u) -> VTyEq (t, u, do_el env a)
  | VTmNeutral n -> VTyEl n
  | _ -> raise (Elab_error "do_el: expected type code or neutral")

and eval_tm (env : env) : tm -> vl_tm = function
  | TmVar idx -> List.nth env idx
  | TmLam (x, a, _, body) -> VTmLam (x, eval_ty env a, ClosTm (env, body))
  | TmApp (f, a) -> do_app (eval_tm env f) (eval_tm env a)
  | TmPiHat (x, a, b) -> VTmPiHat (x, eval_tm env a, ClosTm (env, b))
  | TmSigmaHat (x, a, b) -> VTmSigmaHat (x, eval_tm env a, ClosTm (env, b))
  | TmMkSigma (a, b, t, u) ->
      VTmMkSigma
        (None, eval_ty env a, ClosTy (env, b), eval_tm env t, eval_tm env u)
  | TmProj1 p -> do_proj1 (eval_tm env p)
  | TmProj2 p -> do_proj2 (eval_tm env p)
  | TmUnit -> VTmUnit
  | TmAbsurd (c, e) -> VTmAbsurd (eval_ty env c, eval_tm env e)
  | TmIntLit n -> VTmIntLit n
  | TmUnitHat -> VTmUnitHat
  | TmEmptyHat -> VTmEmptyHat
  | TmIntHat -> VTmIntHat
  | TmEqHat (a, t, u) -> VTmEqHat (eval_tm env a, eval_tm env t, eval_tm env u)
  | TmRefl (a, e) -> VTmRefl (eval_ty env a, eval_tm env e)
  | TmAdd (a, b) -> do_add (eval_tm env a, eval_tm env b)
  | TmSub (a, b) -> do_sub (eval_tm env a, eval_tm env b)
  | TmSorry ty -> VTmSorry (eval_ty env ty)
  | TmLet (_, _, t, body) -> eval_tm (eval_tm env t :: env) body

and do_add : vl_tm * vl_tm -> vl_tm = function
  | VTmIntLit n, VTmIntLit m -> VTmIntLit (n + m)
  | a, b -> VTmAdd (a, b)

and do_sub : vl_tm * vl_tm -> vl_tm = function
  | VTmIntLit n, VTmIntLit m -> VTmIntLit (n - m)
  | a, b -> VTmSub (a, b)

and do_app (f : vl_tm) (a : vl_tm) : vl_tm =
  match f with
  | VTmLam (_, _, ClosTm (env, body)) -> eval_tm (a :: env) body
  | VTmNeutral (h, sp) -> VTmNeutral (h, sp @ [ FApp a ])
  | _ -> raise (Elab_error "do_app: expected lambda or neutral")

and do_proj1 : vl_tm -> vl_tm = function
  | VTmMkSigma (_, _, _, t, _) -> t
  | VTmNeutral (h, sp) -> VTmNeutral (h, sp @ [ FProj1 ])
  | _ -> raise (Elab_error "do_proj1: expected pair or neutral")

and do_proj2 : vl_tm -> vl_tm = function
  | VTmMkSigma (_, _, _, _, u) -> u
  | VTmNeutral (h, sp) -> VTmNeutral (h, sp @ [ FProj2 ])
  | _ -> raise (Elab_error "do_proj2: expected pair or neutral")

(* ========== Quoting ========== *)

let lvl_to_ix (l : lvl) (x : lvl) : lvl = l - x - 1

let rec quote_ty (l : lvl) : vl_ty -> ty = function
  | VTyU -> TyU
  | VTyPi (x, a, ClosTy (env, body)) ->
      let a' = quote_ty l a in
      let var = VTmNeutral (HVar l, []) in
      let b' = quote_ty (l + 1) (eval_ty (var :: env) body) in
      TyPi (x, a', b')
  | VTySigma (x, a, ClosTy (env, body)) ->
      let a' = quote_ty l a in
      let var = VTmNeutral (HVar l, []) in
      let b' = quote_ty (l + 1) (eval_ty (var :: env) body) in
      TySigma (x, a', b')
  | VTyUnit -> TyUnit
  | VTyEmpty -> TyEmpty
  | VTyInt -> TyInt
  | VTyEq (e1, e2, a) -> TyEq (quote_tm l e1, quote_tm l e2, quote_ty l a)
  | VTyEl n -> TyEl (quote_neutral l n)

and quote_tm (l : lvl) : vl_tm -> tm = function
  | VTmNeutral n -> quote_neutral l n
  | VTmLam (x, a, ClosTm (env, body)) ->
      let var = VTmNeutral (HVar l, []) in
      let a = quote_ty l a in
      let b = quote_ty (l + 1) VTyU in
      let body' = quote_tm (l + 1) (eval_tm (var :: env) body) in
      TmLam (x, a, b, body')
  | VTmPiHat (x, a, ClosTm (env, body)) ->
      let a = quote_tm l a in
      let var = VTmNeutral (HVar l, []) in
      let b = quote_tm (l + 1) (eval_tm (var :: env) body) in
      TmPiHat (x, a, b)
  | VTmSigmaHat (x, a, ClosTm (env, body)) ->
      let a = quote_tm l a in
      let var = VTmNeutral (HVar l, []) in
      let b = quote_tm (l + 1) (eval_tm (var :: env) body) in
      TmSigmaHat (x, a, b)
  | VTmMkSigma (x, a_ty, ClosTy (env, body), t, u) ->
      let a = quote_ty l a_ty in
      let var = VTmNeutral (HVar l, []) in
      let b = quote_ty (l + 1) (eval_ty (var :: env) body) in
      ignore x;
      TmMkSigma (a, b, quote_tm l t, quote_tm l u)
  | VTmUnit -> TmUnit
  | VTmAbsurd (c, e) -> TmAbsurd (quote_ty l c, quote_tm l e)
  | VTmIntLit n -> TmIntLit n
  | VTmUnitHat -> TmUnitHat
  | VTmEmptyHat -> TmEmptyHat
  | VTmIntHat -> TmIntHat
  | VTmEqHat (a, t, u) -> TmEqHat (quote_tm l a, quote_tm l t, quote_tm l u)
  | VTmRefl (a, e) -> TmRefl (quote_ty l a, quote_tm l e)
  | VTmAdd (a, b) -> TmAdd (quote_tm l a, quote_tm l b)
  | VTmSub (a, b) -> TmSub (quote_tm l a, quote_tm l b)
  | VTmSorry ty -> TmSorry (quote_ty l ty)

and quote_neutral (l : lvl) ((h, sp) : neutral) : tm =
  let head_tm =
    match h with
    | HVar x -> TmVar (lvl_to_ix l x)
    | HConst _ -> raise (Elab_error "quote_neutral: globals not yet supported")
  in
  quote_spine l head_tm sp

and quote_spine (l : lvl) (tm : tm) : spine -> tm = function
  | [] -> tm
  | FApp a :: rest -> quote_spine l (TmApp (tm, quote_tm l a)) rest
  | FProj1 :: rest -> quote_spine l (TmProj1 tm) rest
  | FProj2 :: rest -> quote_spine l (TmProj2 tm) rest

let nf_ty (env : env) (t : ty) : ty = quote_ty (List.length env) (eval_ty env t)
let nf_tm (env : env) (t : tm) : tm = quote_tm (List.length env) (eval_tm env t)

let rec ty_to_code : ty -> tm = function
  | TyUnit -> TmUnitHat
  | TyEmpty -> TmEmptyHat
  | TyInt -> TmIntHat
  | TyEl t -> t
  | TyPi (x, a, b) -> TmPiHat (x, ty_to_code a, ty_to_code b)
  | TySigma (x, a, b) -> TmSigmaHat (x, ty_to_code a, ty_to_code b)
  | TyEq (a, b, t) -> TmEqHat (ty_to_code t, a, b)
  | TyU -> raise (Elab_error "ty_to_code: U has no code")

(* ========== Context Module ========== *)

module Context = struct
  type binding = {
    name : string option;
    ty : vl_ty;
  }

  type t = {
    bindings : binding list;
    env : env;
  }

  let lvl (ctx : t) : lvl = List.length ctx.bindings
  let empty : t = { bindings = []; env = [] }
  let env (ctx : t) : env = ctx.env

  let bind (name : string option) (ty : vl_ty) (ctx : t) : t =
    let var = VTmNeutral (HVar (lvl ctx), []) in
    { bindings = { name; ty } :: ctx.bindings; env = var :: ctx.env }

  let define (name : string) (ty : vl_ty) (value : vl_tm) (ctx : t) : t =
    {
      bindings = { name = Some name; ty } :: ctx.bindings;
      env = value :: ctx.env;
    }

  let lookup_var (name : string) (ctx : t) : (lvl * vl_ty) option =
    List.find_mapi
      (fun i b ->
        Option.bind b.name (fun bn ->
            if String.equal bn name then
              Some (lvl ctx - i - 1, b.ty)
            else
              None))
      ctx.bindings

  let pp (fmt : Format.formatter) (ctx : t) : unit =
    let names =
      List.map (fun b -> Option.value b.name ~default:"_") ctx.bindings
    in
    let pp_binding fmt (b : binding) =
      let name = Option.value b.name ~default:"_" in
      let ty = quote_ty (List.length ctx.bindings) b.ty in
      Format.fprintf fmt "%s : %a" name (Pretty.pp_ty_ctx names) ty
    in
    Format.fprintf fmt "[%a]"
      (Format.pp_print_list
         ~pp_sep:(fun fmt () -> Format.fprintf fmt ", ")
         pp_binding)
      ctx.bindings
end

(* Γ ⊢ A ≡ B type *)
let rec eq_ty (l : lvl) : vl_ty * vl_ty -> bool = function
  | VTyU, VTyU -> true
  | VTyPi (_, a1, ClosTy (env1, body1)), VTyPi (_, a2, ClosTy (env2, body2)) ->
      eq_ty l (a1, a2)
      &&
      let var = VTmNeutral (HVar l, []) in
      eq_ty (l + 1) (eval_ty (var :: env1) body1, eval_ty (var :: env2) body2)
  | ( VTySigma (_, a1, ClosTy (env1, body1)),
      VTySigma (_, a2, ClosTy (env2, body2)) ) ->
      eq_ty l (a1, a2)
      &&
      let var = VTmNeutral (HVar l, []) in
      eq_ty (l + 1) (eval_ty (var :: env1) body1, eval_ty (var :: env2) body2)
  | VTyUnit, VTyUnit -> true
  | VTyEmpty, VTyEmpty -> true
  | VTyInt, VTyInt -> true
  | VTyEq (e1, e2, a), VTyEq (e1', e2', a') ->
      eq_tm l (e1, e1') && eq_tm l (e2, e2') && eq_ty l (a, a')
  | VTyEl n1, VTyEl n2 -> eq_neutral l n1 n2
  | _, _ -> false

(* Γ ⊢ t ≡ u term *)
and eq_tm (l : lvl) : vl_tm * vl_tm -> bool = function
  | VTmNeutral n1, VTmNeutral n2 -> eq_neutral l n1 n2
  | VTmLam (_, _, ClosTm (env1, body1)), VTmLam (_, _, ClosTm (env2, body2)) ->
      let var = VTmNeutral (HVar l, []) in
      eq_tm (l + 1) (eval_tm (var :: env1) body1, eval_tm (var :: env2) body2)
  | VTmLam (_, _, ClosTm (env, body)), t
  | t, VTmLam (_, _, ClosTm (env, body)) ->
      let var = VTmNeutral (HVar l, []) in
      eq_tm (l + 1) (eval_tm (var :: env) body, do_app t var)
  | VTmMkSigma (_, _, _, t1, u1), VTmMkSigma (_, _, _, t2, u2) ->
      eq_tm l (t1, t2) && eq_tm l (u1, u2)
  | VTmMkSigma (_, _, _, t, u), p
  | p, VTmMkSigma (_, _, _, t, u) ->
      eq_tm l (t, do_proj1 p) && eq_tm l (u, do_proj2 p)
  | ( VTmPiHat (_, a1, ClosTm (env1, body1)),
      VTmPiHat (_, a2, ClosTm (env2, body2)) ) ->
      eq_tm l (a1, a2)
      &&
      let var = VTmNeutral (HVar l, []) in
      eq_tm (l + 1) (eval_tm (var :: env1) body1, eval_tm (var :: env2) body2)
  | ( VTmSigmaHat (_, a1, ClosTm (env1, body1)),
      VTmSigmaHat (_, a2, ClosTm (env2, body2)) ) ->
      eq_tm l (a1, a2)
      &&
      let var = VTmNeutral (HVar l, []) in
      eq_tm (l + 1) (eval_tm (var :: env1) body1, eval_tm (var :: env2) body2)
  | VTmUnit, VTmUnit -> true
  | VTmIntLit n1, VTmIntLit n2 -> n1 = n2
  | VTmUnitHat, VTmUnitHat -> true
  | VTmEmptyHat, VTmEmptyHat -> true
  | VTmIntHat, VTmIntHat -> true
  | VTmAbsurd (c1, e1), VTmAbsurd (c2, e2) ->
      eq_ty l (c1, c2) && eq_tm l (e1, e2)
  | VTmEqHat (a1, t1, u1), VTmEqHat (a2, t2, u2) ->
      eq_tm l (a1, a2) && eq_tm l (t1, t2) && eq_tm l (u1, u2)
  | VTmRefl (a1, e1), VTmRefl (a2, e2) -> eq_ty l (a1, a2) && eq_tm l (e1, e2)
  | VTmAdd (a1, b1), VTmAdd (a2, b2) -> eq_tm l (a1, a2) && eq_tm l (b1, b2)
  | VTmSub (a1, b1), VTmSub (a2, b2) -> eq_tm l (a1, a2) && eq_tm l (b1, b2)
  | VTmSorry ty1, VTmSorry ty2 -> eq_ty l (ty1, ty2)
  | _, _ -> false

and eq_neutral (l : lvl) ((h1, sp1) : neutral) ((h2, sp2) : neutral) : bool =
  eq_head (h1, h2) && eq_spine l (sp1, sp2)

and eq_head : head * head -> bool = function
  | HVar x, HVar y -> x = y
  | HConst n1, HConst n2 -> String.equal n1 n2
  | _, _ -> false

and eq_spine (l : lvl) : spine * spine -> bool = function
  | [], [] -> true
  | f1 :: rest1, f2 :: rest2 -> eq_fname l (f1, f2) && eq_spine l (rest1, rest2)
  | _, _ -> false

and eq_fname (l : lvl) : fname * fname -> bool = function
  | FApp a1, FApp a2 -> eq_tm l (a1, a2)
  | FProj1, FProj1 -> true
  | FProj2, FProj2 -> true
  | _, _ -> false

let conv_ty (ctx : Context.t) (a : vl_ty) (b : vl_ty) : unit =
  let lvl = Context.lvl ctx in
  if not (eq_ty lvl (a, b)) then
    let names =
      List.map
        (fun (b : Context.binding) -> Option.value b.name ~default:"_")
        ctx.bindings
    in
    let to_str x =
      Format.asprintf "%a" (Pretty.pp_ty_ctx names) (quote_ty lvl x)
    in
    raise
      (Elab_error
         (Format.sprintf "Type mismatch: expected %s, got %s" (to_str a)
            (to_str b)))

(* Γ ⊢ A type *)
let rec check_ty (ctx : Context.t) : raw -> ty =
  let binders ((names, a) : binder_group) (b : raw)
      (mk : string option -> ty -> ty -> ty) : ty =
    let a' = check_ty ctx a in
    let av = eval_ty (Context.env ctx) a' in
    let rec go ctx = function
      | [] -> check_ty ctx b
      | x :: xs ->
          let ctx' = Context.bind x av ctx in
          mk x a' (go ctx' xs)
    in
    go ctx names
  in
  function
  | RU -> TyU
  | RIdent x -> (
      match Context.lookup_var x ctx with
      | Some (lvl, VTyU) -> TyEl (TmVar (Context.lvl ctx - lvl - 1))
      | Some (_, ty) ->
          raise
            (Elab_error
               (Format.asprintf "Variable %s has type %a, expected U" x
                  Pretty.pp_ty
                  (quote_ty (Context.lvl ctx) ty)))
      | None -> raise (Elab_error ("Type variable not in scope: " ^ x)))
  | RPi (group, b) -> binders group b (fun x a b -> TyPi (x, a, b))
  | RArrow (a, b) -> binders ([ None ], a) b (fun x a b -> TyPi (x, a, b))
  | RSigma (group, b) -> binders group b (fun x a b -> TySigma (x, a, b))
  | RProd (a, b) -> binders ([ None ], a) b (fun x a b -> TySigma (x, a, b))
  | RUnit -> TyUnit
  | REmpty -> TyEmpty
  | RInt -> TyInt
  | REq (a, b) ->
      let a, ty = infer_tm ctx a in
      TyEq (a, check_tm ctx b ty, quote_ty (Context.lvl ctx) ty)
  | (RApp (_, _) | RAnn (_, _)) as e -> TyEl (check_tm ctx e VTyU)
  | ( RUnitTm | RSorry
    | RLam (_, _)
    | RLet (_, _, _, _)
    | RAbsurd _ | RRefl _
    | RPair (_, _)
    | RProj1 _ | RProj2 _ | RIntLit _
    | RAdd (_, _)
    | RSub (_, _) ) as raw ->
      raise
        (Elab_error
           (Format.asprintf "Expected a type, but got: %a" Pretty.pp_raw raw))

(* Γ ⊢ e ⇐ A *)
and check_tm (ctx : Context.t) (raw : raw) (ty : vl_ty) : tm =
  match (raw, ty) with
  | RLam ([], body), ty -> check_tm ctx body ty
  | RLam ((x, a_ann) :: rest, body), VTyPi (_, a_ty, ClosTy (env, body_ty)) ->
      (match a_ann with
      | Some a_ann_raw ->
          let a' = check_ty ctx a_ann_raw in
          let a_val = eval_ty (Context.env ctx) a' in
          conv_ty ctx a_ty a_val
      | None -> ());
      let var = VTmNeutral (HVar (Context.lvl ctx), []) in
      let ctx' = Context.bind x a_ty ctx in
      let b_val = eval_ty (var :: env) body_ty in
      let b' = quote_ty (Context.lvl ctx') b_val in
      let body' = check_tm ctx' (RLam (rest, body)) b_val in
      TmLam (x, quote_ty (Context.lvl ctx) a_ty, b', body')
  | RPair (a, b), VTySigma (_, a_ty, ClosTy (env, body)) ->
      let a' = check_tm ctx a a_ty in
      let a_val = eval_tm (Context.env ctx) a' in
      let b_ty = eval_ty (a_val :: env) body in
      let b' = check_tm ctx b b_ty in
      let a_ty' = quote_ty (Context.lvl ctx) a_ty in
      let var = VTmNeutral (HVar (Context.lvl ctx), []) in
      let b_ty' = quote_ty (Context.lvl ctx + 1) (eval_ty (var :: env) body) in
      TmMkSigma (a_ty', b_ty', a', b')
  | RRefl e, VTyEq (e1, e2, a) ->
      let e' = check_tm ctx e a in
      let e_val = eval_tm (Context.env ctx) e' in
      let l = Context.lvl ctx in
      if not (eq_tm l (e1, e2)) then
        raise
          (Elab_error "refl: sides of equality are not definitionally equal");
      if not (eq_tm l (e_val, e1)) then
        raise (Elab_error "refl: term does not match the sides of the equality");
      TmRefl (quote_ty l a, e')
  | RUnit, VTyUnit -> TmUnit
  | RAbsurd e, ty ->
      TmAbsurd (quote_ty (Context.lvl ctx) ty, check_tm ctx e VTyEmpty)
  | RSorry, ty -> TmSorry (quote_ty (Context.lvl ctx) ty)
  | RLet (x, ty_opt, t, body), expected_ty -> (
      match ty_opt with
      | Some ty_raw ->
          let ty' = check_ty ctx ty_raw in
          let ty_val = eval_ty (Context.env ctx) ty' in
          let t' = check_tm ctx t ty_val in
          let t_val = eval_tm (Context.env ctx) t' in
          let ctx' = Context.define x ty_val t_val ctx in
          let body' = check_tm ctx' body expected_ty in
          TmLet (x, ty', t', body')
      | None ->
          let t', t_ty = infer_tm ctx t in
          let t_val = eval_tm (Context.env ctx) t' in
          let ctx' = Context.define x t_ty t_val ctx in
          let body' = check_tm ctx' body expected_ty in
          TmLet (x, quote_ty (Context.lvl ctx) t_ty, t', body'))
  | RAnn (e, ty_raw), expected_ty ->
      let ty' = check_ty ctx ty_raw in
      let ty_val = eval_ty (Context.env ctx) ty' in
      conv_ty ctx expected_ty ty_val;
      check_tm ctx e ty_val
  | raw, ty ->
      let t', inferred_ty = infer_tm ctx raw in
      conv_ty ctx ty inferred_ty;
      t'

(* Γ ⊢ e ⇒ A *)
and infer_tm (ctx : Context.t) : raw -> tm * vl_ty =
  let binders ((names, a) : binder_group) (b : raw)
      (mk : string option -> tm -> tm -> tm) =
    let a' = check_tm ctx a VTyU in
    let a_val = eval_tm (Context.env ctx) a' in
    let a_el = do_el (Context.env ctx) a_val in
    let rec go ctx = function
      | [] -> infer_tm ctx b
      | x :: xs ->
          let ctx' = Context.bind x a_el ctx in
          let b', b_ty = go ctx' xs in
          conv_ty ctx' b_ty VTyU;
          (mk x a' b', VTyU)
    in
    go ctx names
  in
  function
  | RIdent x -> (
      match Context.lookup_var x ctx with
      | Some (lvl, ty) -> (TmVar (Context.lvl ctx - lvl - 1), ty)
      | None -> raise (Elab_error ("Variable not in scope: " ^ x)))
  | RApp (f, a) -> (
      let f', f_ty = infer_tm ctx f in
      match f_ty with
      | VTyPi (_, a_ty, ClosTy (env, body)) ->
          let a' = check_tm ctx a a_ty in
          let a_val = eval_tm (Context.env ctx) a' in
          let b_val = eval_ty (a_val :: env) body in
          (TmApp (f', a'), b_val)
      | _ ->
          raise
            (Elab_error
               (Format.asprintf
                  "Application: expected function type, but %a has a different \
                   type"
                  Pretty.pp_raw f)))
  | RProj1 p -> (
      let p', p_ty = infer_tm ctx p in
      match p_ty with
      | VTySigma (_, a, _) -> (TmProj1 p', a)
      | _ ->
          raise
            (Elab_error
               (Format.asprintf
                  "proj1: expected sigma/product type, but %a has a different \
                   type"
                  Pretty.pp_raw p)))
  | RProj2 p -> (
      let p', p_ty = infer_tm ctx p in
      match p_ty with
      | VTySigma (_, _, ClosTy (env, body)) ->
          let proj1_tm = TmProj1 p' in
          let proj1_val = eval_tm (Context.env ctx) proj1_tm in
          let b_val = eval_ty (proj1_val :: env) body in
          (TmProj2 p', b_val)
      | _ ->
          raise
            (Elab_error
               (Format.asprintf
                  "proj2: expected sigma/product type, but %a has a different \
                   type"
                  Pretty.pp_raw p)))
  | RUnitTm -> (TmUnit, VTyUnit)
  | RIntLit n -> (TmIntLit n, VTyInt)
  | RLet (x, ty_opt, t, body) -> (
      match ty_opt with
      | Some ty_raw ->
          let ty' = check_ty ctx ty_raw in
          let ty_val = eval_ty (Context.env ctx) ty' in
          let t' = check_tm ctx t ty_val in
          let t_val = eval_tm (Context.env ctx) t' in
          let ctx' = Context.define x ty_val t_val ctx in
          let body', body_ty = infer_tm ctx' body in
          (TmLet (x, ty', t', body'), body_ty)
      | None ->
          let t', t_ty = infer_tm ctx t in
          let t_val = eval_tm (Context.env ctx) t' in
          let ctx' = Context.define x t_ty t_val ctx in
          let body', body_ty = infer_tm ctx' body in
          (TmLet (x, quote_ty (Context.lvl ctx) t_ty, t', body'), body_ty))
  | RLam ([], body) -> infer_tm ctx body
  | RLam ((_, None) :: _, _) ->
      raise
        (Elab_error "Cannot infer type of unannotated lambda, no unifier :(")
  | RLam ((x, Some ty_raw) :: rest, body) ->
      let a' = check_ty ctx ty_raw in
      let a_val = eval_ty (Context.env ctx) a' in
      let ctx' = Context.bind x a_val ctx in
      let body', b_val = infer_tm ctx' (RLam (rest, body)) in
      let b' = quote_ty (Context.lvl ctx') b_val in
      (TmLam (x, a', b', body'), VTyPi (x, a_val, ClosTy (Context.env ctx, b')))
  | RRefl e ->
      let e', e_ty = infer_tm ctx e in
      let e_val = eval_tm (Context.env ctx) e' in
      (TmRefl (quote_ty (Context.lvl ctx) e_ty, e'), VTyEq (e_val, e_val, e_ty))
  | RPair (a, b) ->
      let a', a_ty = infer_tm ctx a in
      let ctx' = Context.bind None a_ty ctx in
      let b', b_ty = infer_tm ctx b in
      let a_ty' = quote_ty (Context.lvl ctx) a_ty in
      let b_ty' = quote_ty (Context.lvl ctx') b_ty in
      ( TmMkSigma (a_ty', b_ty', a', b'),
        VTySigma (None, a_ty, ClosTy (Context.env ctx, b_ty')) )
  (* Types as terms *)
  | RUnit -> (TmUnitHat, VTyU)
  | REmpty -> (TmEmptyHat, VTyU)
  | RInt -> (TmIntHat, VTyU)
  | RAbsurd _ -> raise (Elab_error "Cannot infer type of absurd")
  | REq (a, b) ->
      let a', a_ty = infer_tm ctx a in
      let b' = check_tm ctx b a_ty in
      let a_ty_quoted = quote_ty (Context.lvl ctx) a_ty in
      let code = ty_to_code a_ty_quoted in
      (TmEqHat (code, a', b'), VTyU)
  | RPi (group, b) -> binders group b (fun x a b -> TmPiHat (x, a, b))
  | RArrow (a, b) -> binders ([ None ], a) b (fun x a b -> TmPiHat (x, a, b))
  | RSigma (group, b) -> binders group b (fun x a b -> TmSigmaHat (x, a, b))
  | RProd (a, b) -> binders ([ None ], a) b (fun x a b -> TmSigmaHat (x, a, b))
  | RAdd (a, b) -> (TmAdd (check_tm ctx a VTyInt, check_tm ctx b VTyInt), VTyInt)
  | RSub (a, b) -> (TmSub (check_tm ctx a VTyInt, check_tm ctx b VTyInt), VTyInt)
  | RAnn (e, ty) ->
      let ty' = check_ty ctx ty in
      let ty_val = eval_ty (Context.env ctx) ty' in
      (check_tm ctx e ty_val, ty_val)
  | RU -> raise (Elab_error "Cannot infer type")
  | RSorry -> raise (Elab_error "Cannot infer type of sorry")

let elab_program : raw_program -> (string * tm * ty) list =
  let rec go acc ctx = function
    | [] -> List.rev acc
    | RDef (name, body) :: rest ->
        let term, ty_val = infer_tm ctx body in
        let term_val = eval_tm (Context.env ctx) term in
        let term_nf = quote_tm 0 term_val in
        let ty_nf = quote_ty 0 ty_val in
        let ctx' = Context.define name ty_val term_val ctx in
        go ((name, term_nf, ty_nf) :: acc) ctx' rest
  in
  go [] Context.empty
