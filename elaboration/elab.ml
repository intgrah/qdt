open Syntax

exception Elab_error of string

let fresh_sorry_id =
  let counter = ref 0 in
  fun () ->
    let id = !counter in
    incr counter;
    id

(* ========== Evaluation ========== *)

let rec eval_ty (env : env) : ty -> vl_ty = function
  | TyU -> VTyU
  | TyPi (x, a, b) -> VTyPi (x, eval_ty env a, ClosTy (env, b))
  | TySigma (x, a, b) -> VTySigma (x, eval_ty env a, ClosTy (env, b))
  | TyUnit -> VTyUnit
  | TyEmpty -> VTyEmpty
  | TyInt -> VTyInt
  | TyEq (e1, e2, a) -> VTyEq (eval_tm env e1, eval_tm env e2, eval_ty env a)
  | TyEl t -> do_el (eval_tm env t)

and do_el : vl_tm -> vl_ty = function
  | VTmPiHat (x, a, ClosTm (env', b)) ->
      VTyPi (x, do_el a, ClosTy (env', TyEl b))
  | VTmSigmaHat (x, a, ClosTm (env', b)) ->
      VTySigma (x, do_el a, ClosTy (env', TyEl b))
  | VTmUnitHat -> VTyUnit
  | VTmEmptyHat -> VTyEmpty
  | VTmIntHat -> VTyInt
  | VTmEqHat (t, u, a) -> VTyEq (t, u, a)
  | VTmNeutral n -> VTyEl n
  | _ -> raise (Elab_error "do_el: expected type code or neutral")

and eval_tm (env : env) : tm -> vl_tm = function
  | TmVar (Idx l) -> List.nth env l
  | TmConst name -> VTmNeutral (HConst name, [])
  | TmLam (x, a, body) -> VTmLam (x, eval_ty env a, ClosTm (env, body))
  | TmApp (f, a) -> do_app (eval_tm env f) (eval_tm env a)
  | TmPiHat (x, a, b) -> VTmPiHat (x, eval_tm env a, ClosTm (env, b))
  | TmSigmaHat (x, a, b) -> VTmSigmaHat (x, eval_tm env a, ClosTm (env, b))
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
  | TmEqHat (t, u, a) -> VTmEqHat (eval_tm env t, eval_tm env u, eval_ty env a)
  | TmRefl (a, e) -> VTmRefl (eval_ty env a, eval_tm env e)
  | TmAdd (a, b) -> (
      match (eval_tm env a, eval_tm env b) with
      | VTmIntLit n, VTmIntLit m -> VTmIntLit (n + m)
      | a, b -> VTmAdd (a, b))
  | TmSub (a, b) -> (
      match (eval_tm env a, eval_tm env b) with
      | VTmIntLit n, VTmIntLit m -> VTmIntLit (n - m)
      | a, b -> VTmSub (a, b))
  | TmSorry (id, ty) -> VTmNeutral (HSorry (id, eval_ty env ty), [])
  | TmLet (_, _, t, body) -> eval_tm (eval_tm env t :: env) body

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

and do_absurd (c : vl_ty) : vl_tm -> vl_tm = function
  | VTmNeutral (h, sp) -> VTmNeutral (h, sp @ [ FAbsurd c ])
  | _ -> raise (Elab_error "do_absurd: expected neutral")

(* ========== Quoting ========== *)

let rec quote_ty (l : int) : vl_ty -> ty = function
  | VTyU -> TyU
  | VTyPi (x, a, ClosTy (env, body)) ->
      let a' = quote_ty l a in
      let var = VTmNeutral (HVar (Lvl l), []) in
      let b' = quote_ty (l + 1) (eval_ty (var :: env) body) in
      TyPi (x, a', b')
  | VTySigma (x, a, ClosTy (env, body)) ->
      let a' = quote_ty l a in
      let var = VTmNeutral (HVar (Lvl l), []) in
      let b' = quote_ty (l + 1) (eval_ty (var :: env) body) in
      TySigma (x, a', b')
  | VTyUnit -> TyUnit
  | VTyEmpty -> TyEmpty
  | VTyInt -> TyInt
  | VTyEq (e1, e2, a) -> TyEq (quote_tm l e1, quote_tm l e2, quote_ty l a)
  | VTyEl n -> TyEl (quote_neutral l n)

and quote_tm (l : int) : vl_tm -> tm = function
  | VTmNeutral n -> quote_neutral l n
  | VTmLam (x, a, ClosTm (env, body)) ->
      let var = VTmNeutral (HVar (Lvl l), []) in
      let a = quote_ty l a in
      let body' = quote_tm (l + 1) (eval_tm (var :: env) body) in
      TmLam (x, a, body')
  | VTmPiHat (x, a, ClosTm (env, body)) ->
      let a = quote_tm l a in
      let var = VTmNeutral (HVar (Lvl l), []) in
      let b = quote_tm (l + 1) (eval_tm (var :: env) body) in
      TmPiHat (x, a, b)
  | VTmSigmaHat (x, a, ClosTm (env, body)) ->
      let a = quote_tm l a in
      let var = VTmNeutral (HVar (Lvl l), []) in
      let b = quote_tm (l + 1) (eval_tm (var :: env) body) in
      TmSigmaHat (x, a, b)
  | VTmMkSigma (_, a_ty, ClosTy (env, body), t, u) ->
      let a = quote_ty l a_ty in
      let var = VTmNeutral (HVar (Lvl l), []) in
      let b = quote_ty (l + 1) (eval_ty (var :: env) body) in
      TmMkSigma (a, b, quote_tm l t, quote_tm l u)
  | VTmUnit -> TmUnit
  | VTmIntLit n -> TmIntLit n
  | VTmUnitHat -> TmUnitHat
  | VTmEmptyHat -> TmEmptyHat
  | VTmIntHat -> TmIntHat
  | VTmEqHat (t, u, a) -> TmEqHat (quote_tm l t, quote_tm l u, quote_ty l a)
  | VTmRefl (a, e) -> TmRefl (quote_ty l a, quote_tm l e)
  | VTmAdd (a, b) -> TmAdd (quote_tm l a, quote_tm l b)
  | VTmSub (a, b) -> TmSub (quote_tm l a, quote_tm l b)

and quote_neutral (l : int) ((h, sp) : neutral) : tm =
  let head_tm =
    match h with
    | HVar x ->
        TmVar (Idx (l - 1 - Lvl.to_int x))
        (* Convert level (x) to index (l - x - 1) *)
    | HConst name -> TmConst name
    | HSorry (id, ty) -> TmSorry (id, quote_ty l ty)
  in
  quote_spine l head_tm sp

and quote_spine (l : int) (tm : tm) : spine -> tm = function
  | [] -> tm
  | FApp a :: rest -> quote_spine l (TmApp (tm, quote_tm l a)) rest
  | FProj1 :: rest -> quote_spine l (TmProj1 tm) rest
  | FProj2 :: rest -> quote_spine l (TmProj2 tm) rest
  | FAbsurd c :: rest -> quote_spine l (TmAbsurd (quote_ty l c, tm)) rest

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

  let lvl (ctx : t) : int = List.length ctx.bindings
  let empty : t = { bindings = []; env = [] }
  let env (ctx : t) : env = ctx.env

  let bind (name : string option) (ty : vl_ty) (ctx : t) : t =
    let var = VTmNeutral (HVar (Lvl (lvl ctx)), []) in
    { bindings = { name; ty } :: ctx.bindings; env = var :: ctx.env }

  let define (name : string) (ty : vl_ty) (value : vl_tm) (ctx : t) : t =
    {
      bindings = { name = Some name; ty } :: ctx.bindings;
      env = value :: ctx.env;
    }

  let lookup_var (name : string) (ctx : t) : (Lvl.t * vl_ty) option =
    List.find_mapi
      (fun i b ->
        Option.bind b.name (fun bn ->
            if String.equal bn name then
              Some (Lvl.Lvl (lvl ctx - i - 1), b.ty)
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

module GlobalEnv = struct
  type entry = {
    ty : vl_ty;
    value : vl_tm;
  }

  type t = (string, entry) Hashtbl.t

  let create () : t = Hashtbl.create 16

  let add (env : t) (name : string) (ty : vl_ty) (value : vl_tm) : unit =
    Hashtbl.add env name { ty; value }

  let find (env : t) (name : string) : entry option = Hashtbl.find_opt env name

  let unfold (env : t) (name : string) : vl_tm option =
    Option.map (fun e -> e.value) (find env name)
end

let rec force_ty (genv : GlobalEnv.t) : vl_ty -> vl_ty = function
  | VTyEl n -> (
      match force_neutral genv n with
      | Some v ->
          let ty = do_el v in
          force_ty genv ty
      | None -> VTyEl n)
  | ty -> ty

and force_neutral (genv : GlobalEnv.t) ((h, sp) : neutral) : vl_tm option =
  match h with
  | HConst name -> (
      match GlobalEnv.unfold genv name with
      | Some v -> Some (apply_spine v sp)
      | None -> None)
  | HVar _ -> None
  | HSorry _ -> None

and apply_spine (v : vl_tm) : spine -> vl_tm = function
  | [] -> v
  | FApp a :: rest -> apply_spine (do_app v a) rest
  | FProj1 :: rest -> apply_spine (do_proj1 v) rest
  | FProj2 :: rest -> apply_spine (do_proj2 v) rest
  | FAbsurd c :: rest -> apply_spine (do_absurd c v) rest

(* Γ ⊢ A ≡ B type *)
and eq_ty (genv : GlobalEnv.t) (l : int) ((ty1, ty2) : vl_ty * vl_ty) : bool =
  match (ty1, ty2) with
  | VTyU, VTyU -> true
  | VTyPi (_, a1, ClosTy (env1, body1)), VTyPi (_, a2, ClosTy (env2, body2)) ->
      eq_ty genv l (a1, a2)
      &&
      let var = VTmNeutral (HVar (Lvl l), []) in
      eq_ty genv (l + 1)
        (eval_ty (var :: env1) body1, eval_ty (var :: env2) body2)
  | ( VTySigma (_, a1, ClosTy (env1, body1)),
      VTySigma (_, a2, ClosTy (env2, body2)) ) ->
      eq_ty genv l (a1, a2)
      &&
      let var = VTmNeutral (HVar (Lvl l), []) in
      eq_ty genv (l + 1)
        (eval_ty (var :: env1) body1, eval_ty (var :: env2) body2)
  | VTyUnit, VTyUnit -> true
  | VTyEmpty, VTyEmpty -> true
  | VTyInt, VTyInt -> true
  | VTyEq (e1, e2, a), VTyEq (e1', e2', a') ->
      eq_tm genv l (e1, e1') && eq_tm genv l (e2, e2') && eq_ty genv l (a, a')
  | VTyEl n1, VTyEl n2 -> eq_neutral genv l n1 n2
  | VTyEl n, ty
  | ty, VTyEl n -> (
      match force_neutral genv n with
      | Some v -> eq_ty genv l (do_el v, ty)
      | None -> false)
  | _, _ -> false

(* Γ ⊢ t ≡ u term *)
and eq_tm (genv : GlobalEnv.t) (l : int) : vl_tm * vl_tm -> bool = function
  | VTmNeutral n1, VTmNeutral n2 -> eq_neutral genv l n1 n2
  | VTmLam (_, _, ClosTm (env1, body1)), VTmLam (_, _, ClosTm (env2, body2)) ->
      let var = VTmNeutral (HVar (Lvl l), []) in
      eq_tm genv (l + 1)
        (eval_tm (var :: env1) body1, eval_tm (var :: env2) body2)
  | VTmLam (_, _, ClosTm (env, body)), t
  | t, VTmLam (_, _, ClosTm (env, body)) ->
      let var = VTmNeutral (HVar (Lvl l), []) in
      eq_tm genv (l + 1) (eval_tm (var :: env) body, do_app t var)
  | VTmMkSigma (_, _, _, t1, u1), VTmMkSigma (_, _, _, t2, u2) ->
      eq_tm genv l (t1, t2) && eq_tm genv l (u1, u2)
  | VTmMkSigma (_, _, _, t, u), p
  | p, VTmMkSigma (_, _, _, t, u) ->
      eq_tm genv l (t, do_proj1 p) && eq_tm genv l (u, do_proj2 p)
  | ( VTmPiHat (_, a1, ClosTm (env1, body1)),
      VTmPiHat (_, a2, ClosTm (env2, body2)) ) ->
      eq_tm genv l (a1, a2)
      &&
      let var = VTmNeutral (HVar (Lvl l), []) in
      eq_tm genv (l + 1)
        (eval_tm (var :: env1) body1, eval_tm (var :: env2) body2)
  | ( VTmSigmaHat (_, a1, ClosTm (env1, body1)),
      VTmSigmaHat (_, a2, ClosTm (env2, body2)) ) ->
      eq_tm genv l (a1, a2)
      &&
      let var = VTmNeutral (HVar (Lvl l), []) in
      eq_tm genv (l + 1)
        (eval_tm (var :: env1) body1, eval_tm (var :: env2) body2)
  | VTmUnit, VTmUnit -> true
  | VTmIntLit n1, VTmIntLit n2 -> n1 = n2
  | VTmUnitHat, VTmUnitHat -> true
  | VTmEmptyHat, VTmEmptyHat -> true
  | VTmIntHat, VTmIntHat -> true
  | VTmEqHat (t1, u1, a1), VTmEqHat (t2, u2, a2) ->
      eq_tm genv l (t1, t2) && eq_tm genv l (u1, u2) && eq_ty genv l (a1, a2)
  | VTmRefl (a1, e1), VTmRefl (a2, e2) ->
      eq_ty genv l (a1, a2) && eq_tm genv l (e1, e2)
  | VTmAdd (a1, b1), VTmAdd (a2, b2) ->
      eq_tm genv l (a1, a2) && eq_tm genv l (b1, b2)
  | VTmSub (a1, b1), VTmSub (a2, b2) ->
      eq_tm genv l (a1, a2) && eq_tm genv l (b1, b2)
  | VTmNeutral n, t
  | t, VTmNeutral n -> (
      match force_neutral genv n with
      | Some v -> eq_tm genv l (v, t)
      | None -> false)
  | _, _ -> false

and eq_neutral (genv : GlobalEnv.t) (l : int) ((h1, sp1) : neutral)
    ((h2, sp2) : neutral) : bool =
  if eq_head (h1, h2) && eq_spine genv l (sp1, sp2) then
    true
  else
    match
      (force_neutral genv (h1, sp1), force_neutral genv (h2, sp2))
    with
    | Some v1, Some v2 -> eq_tm genv l (v1, v2)
    | Some v1, None -> eq_tm genv l (v1, VTmNeutral (h2, sp2))
    | None, Some v2 -> eq_tm genv l (VTmNeutral (h1, sp1), v2)
    | None, None -> false

and eq_head : head * head -> bool = function
  | HVar x, HVar y -> x = y
  | HConst n1, HConst n2 -> String.equal n1 n2
  | HSorry (id1, _), HSorry (id2, _) -> id1 = id2
  | _, _ -> false

and eq_spine (genv : GlobalEnv.t) (l : int) : spine * spine -> bool = function
  | [], [] -> true
  | f1 :: rest1, f2 :: rest2 ->
      eq_fname genv l (f1, f2) && eq_spine genv l (rest1, rest2)
  | _, _ -> false

and eq_fname (genv : GlobalEnv.t) (l : int) : fname * fname -> bool = function
  | FApp a1, FApp a2 -> eq_tm genv l (a1, a2)
  | FProj1, FProj1 -> true
  | FProj2, FProj2 -> true
  | FAbsurd c1, FAbsurd c2 -> eq_ty genv l (c1, c2)
  | _, _ -> false

let conv_ty (genv : GlobalEnv.t) (ctx : Context.t) (a : vl_ty) (b : vl_ty) :
    unit =
  let lvl = Context.lvl ctx in
  if not (eq_ty genv lvl (a, b)) then
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
let rec check_ty (genv : GlobalEnv.t) (ctx : Context.t) : Raw.t -> ty =
  let binders ((names, a) : Raw.binder_group) (b : Raw.t)
      (mk : string option -> ty -> ty -> ty) : ty =
    let a' = check_ty genv ctx a in
    let av = eval_ty (Context.env ctx) a' in
    let rec go ctx = function
      | [] -> check_ty genv ctx b
      | x :: xs ->
          let ctx' = Context.bind x av ctx in
          mk x a' (go ctx' xs)
    in
    go ctx names
  in
  function
  | U -> TyU
  | Ident x -> (
      match Context.lookup_var x ctx with
      | Some (Lvl lvl, VTyU) -> TyEl (TmVar (Idx (Context.lvl ctx - 1 - lvl)))
      | Some (_, ty) ->
          raise
            (Elab_error
               (Format.asprintf "Variable %s has type %a, expected U" x
                  Pretty.pp_ty
                  (quote_ty (Context.lvl ctx) ty)))
      | None -> (
          match GlobalEnv.find genv x with
          | Some { ty = VTyU; _ } -> TyEl (TmConst x)
          | Some { ty; _ } ->
              raise
                (Elab_error
                   (Format.asprintf "Global %s has type %a, expected U" x
                      Pretty.pp_ty
                      (quote_ty (Context.lvl ctx) ty)))
          | None ->
              raise
                (Elab_error (Format.sprintf "Type variable not in scope: %s" x))
          ))
  | Pi (group, b) -> binders group b (fun x a b -> TyPi (x, a, b))
  | Arrow (a, b) -> binders ([ None ], a) b (fun x a b -> TyPi (x, a, b))
  | Sigma (group, b) -> binders group b (fun x a b -> TySigma (x, a, b))
  | Prod (a, b) -> binders ([ None ], a) b (fun x a b -> TySigma (x, a, b))
  | Unit -> TyUnit
  | Empty -> TyEmpty
  | Int -> TyInt
  | Eq (a, b) ->
      let a, ty = infer_tm genv ctx a in
      TyEq (a, check_tm genv ctx b ty, quote_ty (Context.lvl ctx) ty)
  | (App (_, _) | Ann (_, _) | Let (_, _, _, _) | Proj1 _ | Proj2 _) as e ->
      TyEl (check_tm genv ctx e VTyU)
  | ( UnitTm | Sorry
    | Lam (_, _)
    | Absurd _ | Refl _
    | Pair (_, _)
    | IntLit _
    | Add (_, _)
    | Sub (_, _) ) as raw ->
      raise
        (Elab_error
           (Format.asprintf "Expected a type, but got: %a" Pretty.pp_raw raw))

(* Γ ⊢ e ⇐ A *)
and check_tm (genv : GlobalEnv.t) (ctx : Context.t) (raw : Raw.t) (ty : vl_ty) :
    tm =
  let ty = force_ty genv ty in
  match (raw, ty) with
  | Lam ([], body), ty -> check_tm genv ctx body ty
  | Lam ((x, a_ann) :: rest, body), VTyPi (_, a_ty, ClosTy (env, body_ty)) ->
      (match a_ann with
      | Some a_ann_raw ->
          let a' = check_ty genv ctx a_ann_raw in
          let a_val = eval_ty (Context.env ctx) a' in
          conv_ty genv ctx a_ty a_val
      | None -> ());
      let var = VTmNeutral (HVar (Lvl.Lvl (Context.lvl ctx)), []) in
      let ctx' = Context.bind x a_ty ctx in
      let b_val = eval_ty (var :: env) body_ty in
      let body' = check_tm genv ctx' (Raw.Lam (rest, body)) b_val in
      TmLam (x, quote_ty (Context.lvl ctx) a_ty, body')
  | Pair (a, b), VTySigma (_, a_ty, ClosTy (env, body)) ->
      let a' = check_tm genv ctx a a_ty in
      let a_val = eval_tm (Context.env ctx) a' in
      let b_ty = eval_ty (a_val :: env) body in
      let b' = check_tm genv ctx b b_ty in
      let a_ty' = quote_ty (Context.lvl ctx) a_ty in
      let var = VTmNeutral (HVar (Lvl (Context.lvl ctx)), []) in
      let b_ty' = quote_ty (Context.lvl ctx + 1) (eval_ty (var :: env) body) in
      TmMkSigma (a_ty', b_ty', a', b')
  | Refl e, VTyEq (e1, e2, a) ->
      let e' = check_tm genv ctx e a in
      let e_val = eval_tm (Context.env ctx) e' in
      let l = Context.lvl ctx in
      if not (eq_tm genv l (e1, e2)) then
        raise
          (Elab_error "refl: sides of equality are not definitionally equal");
      if not (eq_tm genv l (e_val, e1)) then
        raise (Elab_error "refl: term does not match the sides of the equality");
      TmRefl (quote_ty l a, e')
  | Unit, VTyUnit -> TmUnit
  | Absurd e, ty ->
      TmAbsurd (quote_ty (Context.lvl ctx) ty, check_tm genv ctx e VTyEmpty)
  | Sorry, ty -> TmSorry (fresh_sorry_id (), quote_ty (Context.lvl ctx) ty)
  | Let (x, ty_opt, t, body), expected_ty -> (
      match ty_opt with
      | Some ty_raw ->
          let ty' = check_ty genv ctx ty_raw in
          let ty_val = eval_ty (Context.env ctx) ty' in
          let t' = check_tm genv ctx t ty_val in
          let t_val = eval_tm (Context.env ctx) t' in
          let ctx' = Context.define x ty_val t_val ctx in
          let body' = check_tm genv ctx' body expected_ty in
          TmLet (x, ty', t', body')
      | None ->
          let t', t_ty = infer_tm genv ctx t in
          let t_val = eval_tm (Context.env ctx) t' in
          let ctx' = Context.define x t_ty t_val ctx in
          let body' = check_tm genv ctx' body expected_ty in
          TmLet (x, quote_ty (Context.lvl ctx) t_ty, t', body'))
  | Ann (e, ty_raw), expected_ty ->
      let ty' = check_ty genv ctx ty_raw in
      let ty_val = eval_ty (Context.env ctx) ty' in
      conv_ty genv ctx expected_ty ty_val;
      check_tm genv ctx e ty_val
  | raw, ty ->
      let t', inferred_ty = infer_tm genv ctx raw in
      conv_ty genv ctx ty inferred_ty;
      t'

(* Γ ⊢ e ⇒ A *)
and infer_tm (genv : GlobalEnv.t) (ctx : Context.t) : Raw.t -> tm * vl_ty =
  let binders ((names, a) : Raw.binder_group) (b : Raw.t)
      (mk : string option -> tm -> tm -> tm) =
    let a' = check_tm genv ctx a VTyU in
    let a_val = eval_tm (Context.env ctx) a' in
    let a_el = do_el a_val in
    let rec go ctx = function
      | [] -> infer_tm genv ctx b
      | x :: xs ->
          let ctx' = Context.bind x a_el ctx in
          let b', b_ty = go ctx' xs in
          conv_ty genv ctx' b_ty VTyU;
          (mk x a' b', VTyU)
    in
    go ctx names
  in
  function
  | Ident x -> (
      match Context.lookup_var x ctx with
      | Some (Lvl lvl, ty) -> (TmVar (Idx (Context.lvl ctx - 1 - lvl)), ty)
      | None -> (
          match GlobalEnv.find genv x with
          | Some entry -> (TmConst x, entry.ty)
          | None ->
              raise (Elab_error (Format.sprintf "Variable not in scope: %s" x)))
      )
  | App (f, a) -> (
      let f', f_ty = infer_tm genv ctx f in
      match force_ty genv f_ty with
      | VTyPi (_, a_ty, ClosTy (env, body)) ->
          let a' = check_tm genv ctx a a_ty in
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
  | Proj1 p -> (
      let p', p_ty = infer_tm genv ctx p in
      match force_ty genv p_ty with
      | VTySigma (_, a, _) -> (TmProj1 p', a)
      | _ ->
          raise
            (Elab_error
               (Format.asprintf
                  "proj1: expected sigma/product type, but %a has a different \
                   type"
                  Pretty.pp_raw p)))
  | Proj2 p -> (
      let p', p_ty = infer_tm genv ctx p in
      match force_ty genv p_ty with
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
  | UnitTm -> (TmUnit, VTyUnit)
  | IntLit n -> (TmIntLit n, VTyInt)
  | Let (x, ty_opt, t, body) -> (
      match ty_opt with
      | Some ty_raw ->
          let ty' = check_ty genv ctx ty_raw in
          let ty_val = eval_ty (Context.env ctx) ty' in
          let t' = check_tm genv ctx t ty_val in
          let t_val = eval_tm (Context.env ctx) t' in
          let ctx' = Context.define x ty_val t_val ctx in
          let body', body_ty = infer_tm genv ctx' body in
          (TmLet (x, ty', t', body'), body_ty)
      | None ->
          let t', t_ty = infer_tm genv ctx t in
          let t_val = eval_tm (Context.env ctx) t' in
          let ctx' = Context.define x t_ty t_val ctx in
          let body', body_ty = infer_tm genv ctx' body in
          (TmLet (x, quote_ty (Context.lvl ctx) t_ty, t', body'), body_ty))
  | Lam ([], body) -> infer_tm genv ctx body
  | Lam ((_, None) :: _, _) ->
      raise
        (Elab_error "Cannot infer type of unannotated lambda, no unifier :(")
  | Lam ((x, Some ty_raw) :: rest, body) ->
      let a' = check_ty genv ctx ty_raw in
      let a_val = eval_ty (Context.env ctx) a' in
      let ctx' = Context.bind x a_val ctx in
      let body', b_val = infer_tm genv ctx' (Raw.Lam (rest, body)) in
      let b' = quote_ty (Context.lvl ctx') b_val in
      (TmLam (x, a', body'), VTyPi (x, a_val, ClosTy (Context.env ctx, b')))
  | Refl e ->
      let e', e_ty = infer_tm genv ctx e in
      let e_val = eval_tm (Context.env ctx) e' in
      (TmRefl (quote_ty (Context.lvl ctx) e_ty, e'), VTyEq (e_val, e_val, e_ty))
  | Pair (a, b) ->
      let a', a_ty = infer_tm genv ctx a in
      let ctx' = Context.bind None a_ty ctx in
      let b', b_ty = infer_tm genv ctx b in
      let a_ty' = quote_ty (Context.lvl ctx) a_ty in
      let b_ty' = quote_ty (Context.lvl ctx') b_ty in
      ( TmMkSigma (a_ty', b_ty', a', b'),
        VTySigma (None, a_ty, ClosTy (Context.env ctx, b_ty')) )
  (* Types as terms *)
  | Unit -> (TmUnitHat, VTyU)
  | Empty -> (TmEmptyHat, VTyU)
  | Int -> (TmIntHat, VTyU)
  | Absurd _ -> raise (Elab_error "Cannot infer type of absurd")
  | Eq (a, b) ->
      let a', a_ty = infer_tm genv ctx a in
      let b' = check_tm genv ctx b a_ty in
      let a_ty = quote_ty (Context.lvl ctx) a_ty in
      (TmEqHat (a', b', a_ty), VTyU)
  | Pi (group, b) -> binders group b (fun x a b -> TmPiHat (x, a, b))
  | Arrow (a, b) -> binders ([ None ], a) b (fun x a b -> TmPiHat (x, a, b))
  | Sigma (group, b) -> binders group b (fun x a b -> TmSigmaHat (x, a, b))
  | Prod (a, b) -> binders ([ None ], a) b (fun x a b -> TmSigmaHat (x, a, b))
  | Add (a, b) ->
      (TmAdd (check_tm genv ctx a VTyInt, check_tm genv ctx b VTyInt), VTyInt)
  | Sub (a, b) ->
      (TmSub (check_tm genv ctx a VTyInt, check_tm genv ctx b VTyInt), VTyInt)
  | Ann (e, ty) ->
      let ty' = check_ty genv ctx ty in
      let ty_val = eval_ty (Context.env ctx) ty' in
      (check_tm genv ctx e ty_val, ty_val)
  | U -> raise (Elab_error "Cannot infer type of Type")
  | Sorry -> raise (Elab_error "Cannot infer type of sorry")

let elab_program (prog : Raw.program) : (string * tm * ty) list =
  let genv = GlobalEnv.create () in
  let rec go acc ctx = function
    | [] -> List.rev acc
    | Raw.Def (name, body) :: rest ->
        let term, ty_val = infer_tm genv ctx body in
        let term_val = eval_tm (Context.env ctx) term in
        GlobalEnv.add genv name ty_val term_val;
        let ty_out = quote_ty 0 ty_val in
        go ((name, term, ty_out) :: acc) ctx rest
    | Raw.Example body :: rest ->
        let term, ty_val = infer_tm genv ctx body in
        let term_val = eval_tm (Context.env ctx) term in
        let term_nf = quote_tm 0 term_val in
        let ty_nf = quote_ty 0 ty_val in
        ignore term_nf;
        ignore ty_nf;
        go acc ctx rest
  in
  go [] Context.empty prog
