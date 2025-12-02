open Syntax

exception Elab_error of string

(* ========== Substitution ========== *)

let rec subst_ty (b : ty) (u : tm) : ty =
  match b with
  | TyU -> TyU
  | TyPi (x, a, b') -> TyPi (x, subst_ty a u, subst_ty b' u)
  | TyArrow (a, b') -> TyArrow (subst_ty a u, subst_ty b' u)
  | TySigma (x, a, b') -> TySigma (x, subst_ty a u, subst_ty b' u)
  | TyProd (a, b') -> TyProd (subst_ty a u, subst_ty b' u)
  | TyUnit -> TyUnit
  | TyEmpty -> TyEmpty
  | TyInt -> TyInt
  | TyEq (e1, e2, a) -> TyEq (subst_tm e1 u, subst_tm e2 u, subst_ty a u)
  | TyEl a -> TyEl (subst_tm a u)

and subst_tm (t : tm) (u : tm) : tm =
  match t with
  | TmVar 0 -> u
  | TmVar n -> TmVar (n - 1)
  | TmLam (x, a, b, t') -> TmLam (x, subst_ty a u, subst_ty b u, subst_tm t' u)
  | TmApp (f, x) -> TmApp (subst_tm f u, subst_tm x u)
  | TmPiHat (x, a, b) -> TmPiHat (x, subst_tm a u, subst_tm b u)
  | TmArrowHat (a, b) -> TmArrowHat (subst_tm a u, subst_tm b u)
  | TmSigmaHat (x, a, b) -> TmSigmaHat (x, subst_tm a u, subst_tm b u)
  | TmProdHat (a, b) -> TmProdHat (subst_tm a u, subst_tm b u)
  | TmMkSigma (a, b, t', u') ->
      TmMkSigma (subst_ty a u, subst_ty b u, subst_tm t' u, subst_tm u' u)
  | TmProj1 p -> TmProj1 (subst_tm p u)
  | TmProj2 p -> TmProj2 (subst_tm p u)
  | TmUnit -> TmUnit
  | TmAbsurd (c, e) -> TmAbsurd (subst_ty c u, subst_tm e u)
  | TmIntLit n -> TmIntLit n
  | TmUnitHat -> TmUnitHat
  | TmEmptyHat -> TmEmptyHat
  | TmIntHat -> TmIntHat
  | TmEqHat (a, t', u') -> TmEqHat (subst_tm a u, subst_tm t' u, subst_tm u' u)
  | TmRefl (a, e) -> TmRefl (subst_ty a u, subst_tm e u)
  | TmAdd (a, b) -> TmAdd (subst_tm a u, subst_tm b u)
  | TmSub (a, b) -> TmSub (subst_tm a u, subst_tm b u)
  | TmSorry ty -> TmSorry (subst_ty ty u)

(* ========== Evaluation ========== *)

let rec eval_ty (env : env) : ty -> vl_ty = function
  | TyU -> VTyU
  | TyPi (x, a, b) -> VTyPi (x, eval_ty env a, ClosTy (env, b))
  | TyArrow (a, b) -> VTyArrow (eval_ty env a, eval_ty env b)
  | TySigma (x, a, b) -> VTySigma (x, eval_ty env a, ClosTy (env, b))
  | TyProd (a, b) -> VTyProd (eval_ty env a, eval_ty env b)
  | TyUnit -> VTyUnit
  | TyEmpty -> VTyEmpty
  | TyInt -> VTyInt
  | TyEq (e1, e2, a) -> VTyEq (eval_tm env e1, eval_tm env e2, eval_ty env a)
  | TyEl t -> do_el env (eval_tm env t)

and do_el (env : env) : vl_tm -> vl_ty = function
  | VTmPiHat (x, a, ClosTm (env', b)) ->
      VTyPi (x, do_el env a, ClosTy (env', TyEl b))
  | VTmArrowHat (a, b) -> VTyArrow (do_el env a, do_el env b)
  | VTmSigmaHat (x, a, ClosTm (env', b)) ->
      VTySigma (x, do_el env a, ClosTy (env', TyEl b))
  | VTmProdHat (a, b) -> VTyProd (do_el env a, do_el env b)
  | VTmUnitHat -> VTyUnit
  | VTmEmptyHat -> VTyEmpty
  | VTmIntHat -> VTyInt
  | VTmEqHat (a, t, u) -> VTyEq (t, u, do_el env a)
  | VTmNeutral n -> VTyEl n
  | _ -> raise (Elab_error "do_el: expected type code or neutral")

and eval_tm (env : env) : tm -> vl_tm = function
  | TmVar idx ->
      let env_len = List.length env in
      if idx < 0 || idx >= env_len then
        VTmNeutral (HVar (env_len - idx - 1), [])
      else
        List.nth env idx
  | TmLam (x, a, _, body) -> VTmLam (x, eval_ty env a, ClosTm (env, body))
  | TmApp (f, a) -> do_app (eval_tm env f) (eval_tm env a)
  | TmPiHat (x, a, b) -> VTmPiHat (x, eval_tm env a, ClosTm (env, b))
  | TmArrowHat (a, b) -> VTmArrowHat (eval_tm env a, eval_tm env b)
  | TmSigmaHat (x, a, b) -> VTmSigmaHat (x, eval_tm env a, ClosTm (env, b))
  | TmProdHat (a, b) -> VTmProdHat (eval_tm env a, eval_tm env b)
  | TmMkSigma (a, b, t, u) ->
      VTmMkSigma
        (None, eval_ty env a, ClosTy (env, b), eval_tm env t, eval_tm env u)
  | TmProj1 p -> do_proj1 (eval_tm env p)
  | TmProj2 p -> do_proj2 (eval_tm env p)
  | TmUnit -> VTmUnit
  | TmAbsurd (c, e) -> do_absurd (eval_ty env c) (eval_tm env e)
  | TmIntLit n -> VTmIntLit n
  | TmUnitHat -> VTmUnitHat
  | TmEmptyHat -> VTmEmptyHat
  | TmIntHat -> VTmIntHat
  | TmEqHat (a, t, u) -> VTmEqHat (eval_tm env a, eval_tm env t, eval_tm env u)
  | TmRefl (a, e) -> VTmRefl (eval_ty env a, eval_tm env e)
  | TmAdd (a, b) -> do_add (eval_tm env a) (eval_tm env b)
  | TmSub (a, b) -> do_sub (eval_tm env a) (eval_tm env b)
  | TmSorry ty -> VTmSorry (eval_ty env ty)

and do_add (a : vl_tm) (b : vl_tm) : vl_tm =
  match (a, b) with
  | VTmIntLit n, VTmIntLit m -> VTmIntLit (n + m)
  | _ -> VTmAdd (a, b)

and do_sub (a : vl_tm) (b : vl_tm) : vl_tm =
  match (a, b) with
  | VTmIntLit n, VTmIntLit m -> VTmIntLit (n - m)
  | _ -> VTmSub (a, b)

and do_absurd (c : vl_ty) (e : vl_tm) : vl_tm =
  match e with
  | VTmNeutral n -> VTmAbsurd (c, n)
  | _ -> raise (Elab_error "do_absurd: expected neutral")

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

let inst_clos_ty (ClosTy (env, body) : clos_ty) (v : vl_tm) : vl_ty =
  eval_ty (v :: env) body

let inst_clos_tm (ClosTm (env, body) : clos_tm) (v : vl_tm) : vl_tm =
  eval_tm (v :: env) body

(* ========== Quoting ========== *)

let lvl_to_ix (l : lvl) (x : lvl) : lvl = l - x - 1

let rec quote_ty (l : lvl) : vl_ty -> ty = function
  | VTyU -> TyU
  | VTyPi (x, a, clos) ->
      let a' = quote_ty l a in
      let var = VTmNeutral (HVar l, []) in
      let b' = quote_ty (l + 1) (inst_clos_ty clos var) in
      TyPi (x, a', b')
  | VTyArrow (a, b) -> TyArrow (quote_ty l a, quote_ty l b)
  | VTySigma (x, a, clos) ->
      let a' = quote_ty l a in
      let var = VTmNeutral (HVar l, []) in
      let b' = quote_ty (l + 1) (inst_clos_ty clos var) in
      TySigma (x, a', b')
  | VTyProd (a, b) -> TyProd (quote_ty l a, quote_ty l b)
  | VTyUnit -> TyUnit
  | VTyEmpty -> TyEmpty
  | VTyInt -> TyInt
  | VTyEq (e1, e2, a) -> TyEq (quote_tm l e1, quote_tm l e2, quote_ty l a)
  | VTyEl n -> TyEl (quote_neutral l n)

and quote_tm (l : lvl) : vl_tm -> tm = function
  | VTmNeutral n -> quote_neutral l n
  | VTmLam (x, a, clos) ->
      let var = VTmNeutral (HVar l, []) in
      let a = quote_ty l a in
      let b = quote_ty (l + 1) VTyU in
      let body = quote_tm (l + 1) (inst_clos_tm clos var) in
      TmLam (x, a, b, body)
  | VTmPiHat (x, a, clos) ->
      let a = quote_tm l a in
      let var = VTmNeutral (HVar l, []) in
      let b = quote_tm (l + 1) (inst_clos_tm clos var) in
      TmPiHat (x, a, b)
  | VTmArrowHat (a, b) -> TmArrowHat (quote_tm l a, quote_tm l b)
  | VTmSigmaHat (x, a, clos) ->
      let a = quote_tm l a in
      let var = VTmNeutral (HVar l, []) in
      let b = quote_tm (l + 1) (inst_clos_tm clos var) in
      TmSigmaHat (x, a, b)
  | VTmProdHat (a, b) -> TmProdHat (quote_tm l a, quote_tm l b)
  | VTmMkSigma (x, a_ty, clos_b, t, u) ->
      let a = quote_ty l a_ty in
      let var = VTmNeutral (HVar l, []) in
      let b = quote_ty (l + 1) (inst_clos_ty clos_b var) in
      ignore x;
      TmMkSigma (a, b, quote_tm l t, quote_tm l u)
  | VTmUnit -> TmUnit
  | VTmAbsurd (c, n) -> TmAbsurd (quote_ty l c, quote_neutral l n)
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
    | HGlobal _ -> raise (Elab_error "quote_neutral: globals not yet supported")
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
  | TyArrow (a, b) -> TmArrowHat (ty_to_code a, ty_to_code b)
  | TySigma (x, a, b) -> TmSigmaHat (x, ty_to_code a, ty_to_code b)
  | TyProd (a, b) -> TmProdHat (ty_to_code a, ty_to_code b)
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

  let bind_anon = bind None

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
  | VTyPi (_, a1, clos1), VTyPi (_, a2, clos2) ->
      eq_ty l (a1, a2)
      &&
      let var = VTmNeutral (HVar l, []) in
      eq_ty (l + 1) (inst_clos_ty clos1 var, inst_clos_ty clos2 var)
  | VTyArrow (a1, b1), VTyArrow (a2, b2) -> eq_ty l (a1, a2) && eq_ty l (b1, b2)
  | VTyPi (_, a1, clos1), VTyArrow (a2, b2) ->
      eq_ty l (a1, a2)
      &&
      let var = VTmNeutral (HVar l, []) in
      eq_ty (l + 1) (inst_clos_ty clos1 var, b2)
  | VTyArrow (a1, b1), VTyPi (_, a2, clos2) ->
      eq_ty l (a1, a2)
      &&
      let var = VTmNeutral (HVar l, []) in
      eq_ty (l + 1) (b1, inst_clos_ty clos2 var)
  | VTySigma (_, a1, clos1), VTySigma (_, a2, clos2) ->
      eq_ty l (a1, a2)
      &&
      let var = VTmNeutral (HVar l, []) in
      eq_ty (l + 1) (inst_clos_ty clos1 var, inst_clos_ty clos2 var)
  | VTyProd (a1, b1), VTyProd (a2, b2) -> eq_ty l (a1, a2) && eq_ty l (b1, b2)
  | VTySigma (_, a1, clos1), VTyProd (a2, b2) ->
      eq_ty l (a1, a2)
      &&
      let var = VTmNeutral (HVar l, []) in
      eq_ty (l + 1) (inst_clos_ty clos1 var, b2)
  | VTyProd (a1, b1), VTySigma (_, a2, clos2) ->
      eq_ty l (a1, a2)
      &&
      let var = VTmNeutral (HVar l, []) in
      eq_ty (l + 1) (b1, inst_clos_ty clos2 var)
  | VTyUnit, VTyUnit -> true
  | VTyEmpty, VTyEmpty -> true
  | VTyInt, VTyInt -> true
  | VTyEq (e1, e2, a), VTyEq (e1', e2', a') ->
      eq_tm l (e1, e1') && eq_tm l (e2, e2') && eq_ty l (a, a')
  | VTyEl n1, VTyEl n2 -> eq_neutral l n1 n2
  | _ -> false

(* Γ ⊢ t ≡ u term *)
and eq_tm (l : lvl) : vl_tm * vl_tm -> bool = function
  | VTmNeutral n1, VTmNeutral n2 -> eq_neutral l n1 n2
  | VTmLam (_, _, clos1), VTmLam (_, _, clos2) ->
      let var = VTmNeutral (HVar l, []) in
      eq_tm (l + 1) (inst_clos_tm clos1 var, inst_clos_tm clos2 var)
  | VTmPiHat (_, a1, clos1), VTmPiHat (_, a2, clos2) ->
      eq_tm l (a1, a2)
      &&
      let var = VTmNeutral (HVar l, []) in
      eq_tm (l + 1) (inst_clos_tm clos1 var, inst_clos_tm clos2 var)
  | VTmArrowHat (a1, b1), VTmArrowHat (a2, b2) ->
      eq_tm l (a1, a2) && eq_tm l (b1, b2)
  | VTmSigmaHat (_, a1, clos1), VTmSigmaHat (_, a2, clos2) ->
      eq_tm l (a1, a2)
      &&
      let var = VTmNeutral (HVar l, []) in
      eq_tm (l + 1) (inst_clos_tm clos1 var, inst_clos_tm clos2 var)
  | VTmProdHat (a1, b1), VTmProdHat (a2, b2) ->
      eq_tm l (a1, a2) && eq_tm l (b1, b2)
  | VTmMkSigma (_, a1, clos1, t1, u1), VTmMkSigma (_, a2, clos2, t2, u2) ->
      eq_ty l (a1, a2)
      &&
      let var = VTmNeutral (HVar l, []) in
      eq_ty (l + 1) (inst_clos_ty clos1 var, inst_clos_ty clos2 var)
      && eq_tm l (t1, t2)
      && eq_tm l (u1, u2)
  | VTmUnit, VTmUnit -> true
  | VTmIntLit n1, VTmIntLit n2 -> n1 = n2
  | VTmUnitHat, VTmUnitHat -> true
  | VTmEmptyHat, VTmEmptyHat -> true
  | VTmIntHat, VTmIntHat -> true
  | VTmAbsurd (c1, n1), VTmAbsurd (c2, n2) ->
      eq_ty l (c1, c2) && eq_neutral l n1 n2
  | VTmEqHat (a1, t1, u1), VTmEqHat (a2, t2, u2) ->
      eq_tm l (a1, a2) && eq_tm l (t1, t2) && eq_tm l (u1, u2)
  | VTmRefl (a1, e1), VTmRefl (a2, e2) -> eq_ty l (a1, a2) && eq_tm l (e1, e2)
  | VTmAdd (a1, b1), VTmAdd (a2, b2) -> eq_tm l (a1, a2) && eq_tm l (b1, b2)
  | VTmSub (a1, b1), VTmSub (a2, b2) -> eq_tm l (a1, a2) && eq_tm l (b1, b2)
  | VTmSorry ty1, VTmSorry ty2 -> eq_ty l (ty1, ty2)
  | _ -> false

and eq_neutral (l : lvl) ((h1, sp1) : neutral) ((h2, sp2) : neutral) : bool =
  eq_head (h1, h2) && eq_spine l (sp1, sp2)

and eq_head : head * head -> bool = function
  | HVar x, HVar y -> x = y
  | HGlobal n1, HGlobal n2 -> String.equal n1 n2
  | _ -> false

and eq_spine (l : lvl) : spine * spine -> bool = function
  | [], [] -> true
  | FApp a1 :: rest1, FApp a2 :: rest2 ->
      eq_tm l (a1, a2) && eq_spine l (rest1, rest2)
  | FProj1 :: rest1, FProj1 :: rest2 -> eq_spine l (rest1, rest2)
  | FProj2 :: rest1, FProj2 :: rest2 -> eq_spine l (rest1, rest2)
  | _ -> false

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
         (Format.sprintf "Type mismatch: expected %s, got %s" (to_str b)
            (to_str a)))

(* Γ ⊢ A type *)
let rec check_ty (ctx : Context.t) : raw -> ty = function
  | RU -> TyU
  | RIdent x -> (
      match Context.lookup_var x ctx with
      | Some (lvl, VTyU) -> TyEl (TmVar (Context.lvl ctx - lvl - 1))
      | Some (_, ty) ->
          let ty_str =
            Format.asprintf "%a" Pretty.pp_ty (quote_ty (Context.lvl ctx) ty)
          in
          raise
            (Elab_error
               (Format.sprintf "Variable %s has type %s, expected U" x ty_str))
      | None -> raise (Elab_error ("Type variable not in scope: " ^ x)))
  | RPi (x, a, b) ->
      let a = check_ty ctx a in
      let av = eval_ty (Context.env ctx) a in
      let ctx = Context.bind x av ctx in
      let b = check_ty ctx b in
      TyPi (x, a, b)
  | RArrow (a, b) ->
      let a = check_ty ctx a in
      let b = check_ty ctx b in
      TyArrow (a, b)
  | RSigma (x, a, b) ->
      let a = check_ty ctx a in
      let av = eval_ty (Context.env ctx) a in
      let ctx = Context.bind x av ctx in
      let b = check_ty ctx b in
      TySigma (x, a, b)
  | RProd (a, b) ->
      let a = check_ty ctx a in
      let b = check_ty ctx b in
      TyProd (a, b)
  | RUnit -> TyUnit
  | REmpty -> TyEmpty
  | RInt -> TyInt
  | REq (a, b) ->
      let a, ty = infer_tm ctx a in
      let b = check_tm ctx b ty in
      TyEq (a, b, quote_ty (Context.lvl ctx) ty)
  | RApp (f, a) ->
      let tm, ty = infer_tm ctx (RApp (f, a)) in
      conv_ty ctx ty VTyU;
      TyEl tm
  | raw ->
      let raw_str = Format.asprintf "%a" Pretty.pp_raw raw in
      raise (Elab_error (Format.sprintf "Expected a type, but got: %s" raw_str))

(* Γ ⊢ e ⇐ A *)
and check_tm (ctx : Context.t) (raw : raw) (ty : vl_ty) : tm =
  match (raw, ty) with
  | RLam (x, Some ty_raw, body), VTyPi (_, a, clos) ->
      let a_given = check_ty ctx ty_raw in
      let a_given_val = eval_ty (Context.env ctx) a_given in
      conv_ty ctx a a_given_val;
      let var = VTmNeutral (HVar (Context.lvl ctx), []) in
      let ctx = Context.bind x a ctx in
      let b_val = inst_clos_ty clos var in
      let b = quote_ty (Context.lvl ctx) b_val in
      let body = check_tm ctx body b_val in
      TmLam (x, a_given, b, body)
  | RLam (x, None, body), VTyPi (_, a, clos) ->
      let lvl = Context.lvl ctx in
      let var = VTmNeutral (HVar lvl, []) in
      let ctx = Context.bind x a ctx in
      let b_val = inst_clos_ty clos var in
      let b = quote_ty (Context.lvl ctx) b_val in
      let body = check_tm ctx body b_val in
      TmLam (x, quote_ty lvl a, b, body)
  | RLam (x, Some ty_raw, body), VTyArrow (a, b) ->
      let a_given = check_ty ctx ty_raw in
      let a_given_val = eval_ty (Context.env ctx) a_given in
      conv_ty ctx a a_given_val;
      let lvl = Context.lvl ctx in
      let ctx = Context.bind x a ctx in
      let b_ty = quote_ty lvl b in
      let body = check_tm ctx body b in
      TmLam (x, a_given, b_ty, body)
  | RLam (x, None, body), VTyArrow (a, b) ->
      let lvl = Context.lvl ctx in
      let ctx = Context.bind x a ctx in
      let b_ty = quote_ty lvl b in
      let body = check_tm ctx body b in
      TmLam (x, quote_ty lvl a, b_ty, body)
  | RPair (t, u), VTySigma (_, a_ty, clos_b) ->
      let t = check_tm ctx t a_ty in
      let t_val = eval_tm (Context.env ctx) t in
      let b_ty = inst_clos_ty clos_b t_val in
      let u = check_tm ctx u b_ty in
      let a_quoted = quote_ty (Context.lvl ctx) a_ty in
      let var = VTmNeutral (HVar (Context.lvl ctx), []) in
      let b_quoted = quote_ty (Context.lvl ctx + 1) (inst_clos_ty clos_b var) in
      TmMkSigma (a_quoted, b_quoted, t, u)
  | RPair (t, u), VTyProd (a_ty, b_ty) ->
      let t = check_tm ctx t a_ty in
      let u = check_tm ctx u b_ty in
      let a_quoted = quote_ty (Context.lvl ctx) a_ty in
      let b_quoted = quote_ty (Context.lvl ctx) b_ty in
      TmMkSigma (a_quoted, b_quoted, t, u)
  | RRefl e, VTyEq (e1, e2, a) ->
      let e = check_tm ctx e a in
      let e_val = eval_tm (Context.env ctx) e in
      let l = Context.lvl ctx in
      if not (eq_tm l (e1, e2)) then
        raise
          (Elab_error "refl: sides of equality are not definitionally equal");
      if not (eq_tm l (e_val, e1)) then
        raise (Elab_error "refl: term does not match the sides of the equality");
      TmRefl (quote_ty l a, e)
  | RUnit, VTyUnit -> TmUnit
  | RSorry, ty -> TmSorry (quote_ty (Context.lvl ctx) ty)
  | RAnn (e, ty_raw), expected_ty ->
      let ty = check_ty ctx ty_raw in
      let ty_val = eval_ty (Context.env ctx) ty in
      conv_ty ctx expected_ty ty_val;
      check_tm ctx e ty_val
  | raw, ty ->
      let t', inferred_ty = infer_tm ctx raw in
      conv_ty ctx ty inferred_ty;
      t'

(* Γ ⊢ e ⇒ A *)
and infer_tm (ctx : Context.t) : raw -> tm * vl_ty = function
  | RIdent x -> (
      match Context.lookup_var x ctx with
      | Some (lvl, ty) -> (TmVar (Context.lvl ctx - lvl - 1), ty)
      | None -> raise (Elab_error ("Variable not in scope: " ^ x)))
  | RApp (f, a) -> (
      let f', f_ty = infer_tm ctx f in
      match f_ty with
      | VTyPi (_, a_ty, clos) ->
          let a' = check_tm ctx a a_ty in
          let a_val = eval_tm (Context.env ctx) a' in
          let b_val = inst_clos_ty clos a_val in
          (TmApp (f', a'), b_val)
      | VTyArrow (a_ty, b_ty) ->
          let a' = check_tm ctx a a_ty in
          (TmApp (f', a'), b_ty)
      | _ ->
          let f_str = Format.asprintf "%a" Pretty.pp_raw f in
          raise
            (Elab_error
               (Format.sprintf
                  "Application: expected function type, but %s has a different \
                   type"
                  f_str)))
  | RProj1 p -> (
      let p', p_ty = infer_tm ctx p in
      match p_ty with
      | VTySigma (_, a, _) -> (TmProj1 p', a)
      | VTyProd (a, _) -> (TmProj1 p', a)
      | _ ->
          let p_str = Format.asprintf "%a" Pretty.pp_raw p in
          raise
            (Elab_error
               (Format.sprintf
                  "proj1: expected sigma/product type, but %s has a different \
                   type"
                  p_str)))
  | RProj2 p -> (
      let p', p_ty = infer_tm ctx p in
      match p_ty with
      | VTySigma (_, _, clos_b) ->
          let proj1_tm = TmProj1 p' in
          let proj1_val = eval_tm (Context.env ctx) proj1_tm in
          let b_val = inst_clos_ty clos_b proj1_val in
          (TmProj2 p', b_val)
      | VTyProd (_, b) -> (TmProj2 p', b)
      | _ ->
          let p_str = Format.asprintf "%a" Pretty.pp_raw p in
          raise
            (Elab_error
               (Format.sprintf
                  "proj2: expected sigma/product type, but %s has a different \
                   type"
                  p_str)))
  | RUnitTm -> (TmUnit, VTyUnit)
  | RIntLit n -> (TmIntLit n, VTyInt)
  | RLet (x, ty_opt, t, body) -> (
      match ty_opt with
      | Some ty_raw ->
          let ty' = check_ty ctx ty_raw in
          let ty_val = eval_ty (Context.env ctx) ty' in
          let _ = check_tm ctx t ty_val in
          let ctx' = Context.bind (Some x) ty_val ctx in
          infer_tm ctx' body
      | None ->
          let t', t_ty = infer_tm ctx t in
          let _ = eval_tm (Context.env ctx) t' in
          let ctx' = Context.bind (Some x) t_ty ctx in
          infer_tm ctx' body)
  | RLam (_, None, _) ->
      raise
        (Elab_error "Cannot infer type of unannotated lambda, no unifier :(")
  | RLam (x, Some ty_raw, body) ->
      let a = check_ty ctx ty_raw in
      let a_val = eval_ty (Context.env ctx) a in
      let ctx' = Context.bind x a_val ctx in
      let body', b_val = infer_tm ctx' body in
      let b = quote_ty (Context.lvl ctx') b_val in
      (TmLam (x, a, b, body'), VTyPi (x, a_val, ClosTy (Context.env ctx, b)))
  | RRefl e ->
      let e', e_ty = infer_tm ctx e in
      let e_val = eval_tm (Context.env ctx) e' in
      (TmRefl (quote_ty (Context.lvl ctx) e_ty, e'), VTyEq (e_val, e_val, e_ty))
  | RPair (a, b) ->
      let a', a_ty = infer_tm ctx a in
      let b', b_ty = infer_tm ctx b in
      let l = Context.lvl ctx in
      let a_quoted = quote_ty l a_ty in
      let b_quoted = quote_ty l b_ty in
      let prod_ty = VTyProd (a_ty, b_ty) in
      (TmMkSigma (a_quoted, b_quoted, a', b'), prod_ty)
  (* Types as terms *)
  | RUnit -> (TmUnitHat, VTyU)
  | REmpty -> (TmEmptyHat, VTyU)
  | RInt -> (TmIntHat, VTyU)
  | RAbsurd (c, e) ->
      let c' = check_ty ctx c in
      let c_val = eval_ty (Context.env ctx) c' in
      let e' = check_tm ctx e VTyEmpty in
      (TmAbsurd (c', e'), c_val)
  | REq (a, b) ->
      let a', a_ty = infer_tm ctx a in
      let b' = check_tm ctx b a_ty in
      let a_ty_quoted = quote_ty (Context.lvl ctx) a_ty in
      let code = ty_to_code a_ty_quoted in
      (TmEqHat (code, a', b'), VTyU)
  | RPi (x, a, b) ->
      let a', a_ty = infer_tm ctx a in
      conv_ty ctx a_ty VTyU;
      let a_val = eval_tm (Context.env ctx) a' in
      let ctx' = Context.bind x (do_el (Context.env ctx) a_val) ctx in
      let b', b_ty = infer_tm ctx' b in
      conv_ty ctx' b_ty VTyU;
      (TmPiHat (x, a', b'), VTyU)
  | RArrow (a, b) ->
      let a', a_ty = infer_tm ctx a in
      conv_ty ctx a_ty VTyU;
      let b', b_ty = infer_tm ctx b in
      conv_ty ctx b_ty VTyU;
      (TmArrowHat (a', b'), VTyU)
  | RSigma (x, a, b) ->
      let a', a_ty = infer_tm ctx a in
      conv_ty ctx a_ty VTyU;
      let a_val = eval_tm (Context.env ctx) a' in
      let ctx' = Context.bind x (do_el (Context.env ctx) a_val) ctx in
      let b', b_ty = infer_tm ctx' b in
      conv_ty ctx' b_ty VTyU;
      (TmSigmaHat (x, a', b'), VTyU)
  | RProd (a, b) ->
      let a', a_ty = infer_tm ctx a in
      conv_ty ctx a_ty VTyU;
      let b', b_ty = infer_tm ctx b in
      conv_ty ctx b_ty VTyU;
      (TmProdHat (a', b'), VTyU)
  | RAdd (a, b) ->
      let a' = check_tm ctx a VTyInt in
      let b' = check_tm ctx b VTyInt in
      (TmAdd (a', b'), VTyInt)
  | RSub (a, b) ->
      let a' = check_tm ctx a VTyInt in
      let b' = check_tm ctx b VTyInt in
      (TmSub (a', b'), VTyInt)
  | RAnn (e, ty_raw) ->
      let ty = check_ty ctx ty_raw in
      let ty_val = eval_ty (Context.env ctx) ty in
      let e = check_tm ctx e ty_val in
      (e, ty_val)
  | RU -> raise (Elab_error "Cannot infer type")
  | RSorry -> raise (Elab_error "Cannot infer type of sorry")

let elab_program (program : raw_program) : (string * tm * ty) list =
  let rec go defs acc ctx =
    match defs with
    | [] -> List.rev acc
    | (name, body) :: rest ->
        let term, ty_val = infer_tm ctx body in
        let term_val = eval_tm (Context.env ctx) term in
        let term_nf = quote_tm 0 term_val in
        let ty_nf = quote_ty 0 ty_val in
        let ctx' = Context.define name ty_val term_val ctx in
        go rest ((name, term_nf, ty_nf) :: acc) ctx'
  in
  go program [] Context.empty
