open Syntax

exception Elab_error of string

let fresh_sorry_id =
  let counter = ref 0 in
  fun () ->
    let id = !counter in
    incr counter;
    id

(* Global environment reference for evaluation unfolding *)
let current_genv : (string -> vl_tm option) ref = ref (fun _ -> None)

let current_recursor_lookup : (string -> recursor_info option) ref =
  ref (fun _ -> None)

let current_ctor_lookup : (string -> (string * int) option) ref =
  ref (fun _ -> None)

(* ========== Evaluation ========== *)

let rec eval_ty (env : env) : ty -> vl_ty = function
  | TyU -> VTyU
  | TyPi (x, a, b) -> VTyPi (x, eval_ty env a, ClosTy (env, b))
  | TySigma (x, a, b) -> VTySigma (x, eval_ty env a, ClosTy (env, b))
  | TyInt -> VTyInt
  | TyEl t -> do_el (eval_tm env t)

and do_el : vl_tm -> vl_ty = function
  | VTmPiHat (x, a, ClosTm (env', b)) ->
      VTyPi (x, do_el a, ClosTy (env', TyEl b))
  | VTmSigmaHat (x, a, ClosTm (env', b)) ->
      VTySigma (x, do_el a, ClosTy (env', TyEl b))
  | VTmIntHat -> VTyInt
  | VTmNeutral n -> VTyEl n
  | _ -> raise (Elab_error "do_el: expected type code or neutral")

and eval_tm (env : env) : tm -> vl_tm = function
  | TmVar (Idx l) -> List.nth env l
  | TmConst name -> (
      match !current_genv name with
      | Some v -> v
      | None -> VTmNeutral (HConst name, []))
  | TmLam (x, a, body) -> VTmLam (x, eval_ty env a, ClosTm (env, body))
  | TmApp (f, a) -> do_app (eval_tm env f) (eval_tm env a)
  | TmPiHat (x, a, b) -> VTmPiHat (x, eval_tm env a, ClosTm (env, b))
  | TmSigmaHat (x, a, b) -> VTmSigmaHat (x, eval_tm env a, ClosTm (env, b))
  | TmMkSigma (a, b, t, u) ->
      VTmMkSigma
        (None, eval_ty env a, ClosTy (env, b), eval_tm env t, eval_tm env u)
  | TmProj1 p -> do_proj1 (eval_tm env p)
  | TmProj2 p -> do_proj2 (eval_tm env p)
  | TmIntLit n -> VTmIntLit n
  | TmIntHat -> VTmIntHat
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
  | VTmNeutral (h, sp) -> VTmNeutral (h, sp @ [ EApp a ])
  | _ -> raise (Elab_error "do_app: expected lambda or neutral")

and do_proj1 : vl_tm -> vl_tm = function
  | VTmMkSigma (_, _, _, t, _) -> t
  | VTmNeutral (h, sp) -> VTmNeutral (h, sp @ [ EProj1 ])
  | _ -> raise (Elab_error "do_proj1: expected pair or neutral")

and do_proj2 : vl_tm -> vl_tm = function
  | VTmMkSigma (_, _, _, _, u) -> u
  | VTmNeutral (h, sp) -> VTmNeutral (h, sp @ [ EProj2 ])
  | _ -> raise (Elab_error "do_proj2: expected pair or neutral")

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
  | VTyInt -> TyInt
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
  | VTmMkSigma (x, a, ClosTy (env, b), t, u) ->
      let a = quote_ty l a in
      let var = VTmNeutral (HVar (Lvl l), []) in
      let b = quote_ty (l + 1) (eval_ty (var :: env) b) in
      ignore x;
      TmMkSigma (a, b, quote_tm l t, quote_tm l u)
  | VTmIntLit n -> TmIntLit n
  | VTmIntHat -> TmIntHat
  | VTmAdd (a, b) -> TmAdd (quote_tm l a, quote_tm l b)
  | VTmSub (a, b) -> TmSub (quote_tm l a, quote_tm l b)

and quote_neutral (l : int) ((h, sp) : neutral) : tm =
  let head =
    match h with
    | HVar (Lvl k) -> TmVar (Idx (l - k - 1))
    | HConst name -> TmConst name
    | HSorry (id, ty) -> TmSorry (id, quote_ty l ty)
  in
  quote_spine l head sp

and quote_spine (l : int) (head : tm) : spine -> tm = function
  | [] -> head
  | EApp arg :: sp -> quote_spine l (TmApp (head, quote_tm l arg)) sp
  | EProj1 :: sp -> quote_spine l (TmProj1 head) sp
  | EProj2 :: sp -> quote_spine l (TmProj2 head) sp

(* Convert a value type to a term representing its code *)
and reify_ty (l : int) : vl_ty -> tm = function
  | VTyU -> raise (Elab_error "Cannot reify Type as a term")
  | VTyInt -> TmIntHat
  | VTyPi (x, a, ClosTy (env, b)) ->
      let var = VTmNeutral (HVar (Lvl l), []) in
      let a' = reify_ty l a in
      let b_ty = eval_ty (var :: env) b in
      let b' = reify_ty (l + 1) b_ty in
      TmPiHat (x, a', b')
  | VTySigma (x, a, ClosTy (env, b)) ->
      let var = VTmNeutral (HVar (Lvl l), []) in
      let a' = reify_ty l a in
      let b_ty = eval_ty (var :: env) b in
      let b' = reify_ty (l + 1) b_ty in
      TmSigmaHat (x, a', b')
  | VTyEl n -> quote_neutral l n

(* ========== Conversion ========== *)

let rec conv_ty (l : int) (t1 : vl_ty) (t2 : vl_ty) : bool =
  match (t1, t2) with
  | VTyU, VTyU -> true
  | VTyPi (_, a1, ClosTy (env1, b1)), VTyPi (_, a2, ClosTy (env2, b2)) ->
      conv_ty l a1 a2
      &&
      let var = VTmNeutral (HVar (Lvl l), []) in
      conv_ty (l + 1) (eval_ty (var :: env1) b1) (eval_ty (var :: env2) b2)
  | VTySigma (_, a1, ClosTy (env1, b1)), VTySigma (_, a2, ClosTy (env2, b2)) ->
      conv_ty l a1 a2
      &&
      let var = VTmNeutral (HVar (Lvl l), []) in
      conv_ty (l + 1) (eval_ty (var :: env1) b1) (eval_ty (var :: env2) b2)
  | VTyInt, VTyInt -> true
  | VTyEl n1, VTyEl n2 -> conv_neutral l n1 n2
  | _ -> false

and conv_tm (l : int) (t1 : vl_tm) (t2 : vl_tm) : bool =
  match (t1, t2) with
  | VTmNeutral n1, VTmNeutral n2 -> conv_neutral l n1 n2
  | VTmLam (_, _, ClosTm (env1, body1)), VTmLam (_, _, ClosTm (env2, body2)) ->
      let var = VTmNeutral (HVar (Lvl l), []) in
      conv_tm (l + 1)
        (eval_tm (var :: env1) body1)
        (eval_tm (var :: env2) body2)
  | VTmPiHat (_, a1, ClosTm (env1, b1)), VTmPiHat (_, a2, ClosTm (env2, b2)) ->
      conv_tm l a1 a2
      &&
      let var = VTmNeutral (HVar (Lvl l), []) in
      conv_tm (l + 1) (eval_tm (var :: env1) b1) (eval_tm (var :: env2) b2)
  | ( VTmSigmaHat (_, a1, ClosTm (env1, b1)),
      VTmSigmaHat (_, a2, ClosTm (env2, b2)) ) ->
      conv_tm l a1 a2
      &&
      let var = VTmNeutral (HVar (Lvl l), []) in
      conv_tm (l + 1) (eval_tm (var :: env1) b1) (eval_tm (var :: env2) b2)
  | ( VTmMkSigma (_, _, ClosTy (env1, b1), t1, u1),
      VTmMkSigma (_, _, ClosTy (env2, b2), t2, u2) ) ->
      let var = VTmNeutral (HVar (Lvl l), []) in
      conv_ty (l + 1) (eval_ty (var :: env1) b1) (eval_ty (var :: env2) b2)
      && conv_tm l t1 t2 && conv_tm l u1 u2
  | VTmIntLit n1, VTmIntLit n2 -> n1 = n2
  | VTmIntHat, VTmIntHat -> true
  | VTmAdd (a1, b1), VTmAdd (a2, b2) -> conv_tm l a1 a2 && conv_tm l b1 b2
  | VTmSub (a1, b1), VTmSub (a2, b2) -> conv_tm l a1 a2 && conv_tm l b1 b2
  | _ -> false

and conv_neutral (l : int) ((h1, sp1) : neutral) ((h2, sp2) : neutral) : bool =
  conv_head l h1 h2 && conv_spine l sp1 sp2

and conv_head (_l : int) (h1 : head) (h2 : head) : bool =
  match (h1, h2) with
  | HVar l1, HVar l2 -> l1 = l2
  | HConst n1, HConst n2 -> String.equal n1 n2
  | HSorry (id1, _), HSorry (id2, _) -> id1 = id2
  | _ -> false

and conv_spine (l : int) (sp1 : spine) (sp2 : spine) : bool =
  match (sp1, sp2) with
  | [], [] -> true
  | EApp a1 :: sp1', EApp a2 :: sp2' ->
      conv_tm l a1 a2 && conv_spine l sp1' sp2'
  | EProj1 :: sp1', EProj1 :: sp2' -> conv_spine l sp1' sp2'
  | EProj2 :: sp1', EProj2 :: sp2' -> conv_spine l sp1' sp2'
  | _ -> false

(* ========== Global Environment ========== *)

type inductive_info = {
  ind_ty : ty;
  ctors : (string * ty) list;
}

type recursor_info = {
  rec_ind_name : string;
  rec_num_params : int;
  rec_num_indices : int;
  rec_num_motives : int; (* always 1 for now *)
  rec_num_methods : int;
  rec_ctor_names : string list;
}

module GlobalEnv = struct
  type entry =
    | Def of {
        ty : vl_ty;
        tm : vl_tm;
      }
    | Opaque of { ty : vl_ty }
    | Inductive of inductive_info
    | Recursor of {
        ty : vl_ty;
        info : recursor_info;
      }
    | Constructor of {
        ty : vl_ty;
        ind_name : string;
        ctor_idx : int;
      }

  type t = { defs : (string, entry) Hashtbl.t }

  let create () : t = { defs = Hashtbl.create 32 }
  let add env name ty tm = Hashtbl.add env.defs name (Def { ty; tm })
  let add_opaque env name ty = Hashtbl.add env.defs name (Opaque { ty })

  let add_inductive env name ind_ty ctors =
    Hashtbl.add env.defs name (Inductive { ind_ty; ctors })

  let add_recursor env name ty info =
    Hashtbl.add env.defs name (Recursor { ty; info })

  let add_constructor env name ty ind_name ctor_idx =
    Hashtbl.add env.defs name (Constructor { ty; ind_name; ctor_idx })

  let find_ty env name =
    match Hashtbl.find_opt env.defs name with
    | Some (Def { ty; _ }) -> Some ty
    | Some (Opaque { ty }) -> Some ty
    | Some (Inductive { ind_ty; _ }) -> Some (eval_ty [] ind_ty)
    | Some (Recursor { ty; _ }) -> Some ty
    | Some (Constructor { ty; _ }) -> Some ty
    | None -> None

  let find_tm env name =
    match Hashtbl.find_opt env.defs name with
    | Some (Def { tm; _ }) -> Some tm
    | _ -> None

  let find_recursor env name =
    match Hashtbl.find_opt env.defs name with
    | Some (Recursor { info; _ }) -> Some info
    | _ -> None

  let find_constructor env name =
    match Hashtbl.find_opt env.defs name with
    | Some (Constructor { ind_name; ctor_idx; _ }) -> Some (ind_name, ctor_idx)
    | _ -> None

  let is_inductive env name =
    match Hashtbl.find_opt env.defs name with
    | Some (Inductive _) -> true
    | _ -> false

  let find_inductive env name =
    match Hashtbl.find_opt env.defs name with
    | Some (Inductive info) -> Some info
    | _ -> None
end

(* ========== Context ========== *)

module Context = struct
  type entry = {
    name : string option;
    ty : vl_ty;
  }

  type t = {
    entries : entry list;
    env : env;
    lvl : int;
  }

  let empty = { entries = []; env = []; lvl = 0 }
  let env ctx = ctx.env
  let lvl ctx = ctx.lvl

  let bind name ty ctx =
    let var = VTmNeutral (HVar (Lvl ctx.lvl), []) in
    {
      entries = { name; ty } :: ctx.entries;
      env = var :: ctx.env;
      lvl = ctx.lvl + 1;
    }

  let lookup_idx ctx (Idx.Idx k) =
    let e = List.nth ctx.entries k in
    e.ty

  let lookup_name ctx name =
    let rec go k = function
      | [] -> None
      | { name = Some n; ty } :: _ when String.equal n name -> Some (k, ty)
      | _ :: rest -> go (k + 1) rest
    in
    go 0 ctx.entries
end

(* ========== Elaboration ========== *)

let rec check_ty (genv : GlobalEnv.t) (ctx : Context.t) : Raw.t -> ty = function
  | Raw.U -> TyU
  | Raw.Pi ((names, dom), cod) ->
      let dom' = check_ty genv ctx dom in
      let dom_val = eval_ty (Context.env ctx) dom' in
      let rec bind_all ctx = function
        | [] -> check_ty genv ctx cod
        | name :: rest ->
            let ctx' = Context.bind name dom_val ctx in
            let cod' = bind_all ctx' rest in
            TyPi (name, dom', cod')
      in
      bind_all ctx names
  | Raw.Arrow (dom, cod) ->
      let dom' = check_ty genv ctx dom in
      let dom_val = eval_ty (Context.env ctx) dom' in
      let ctx' = Context.bind None dom_val ctx in
      let cod' = check_ty genv ctx' cod in
      TyPi (None, dom', cod')
  | Raw.Sigma ((names, fst_ty), snd_ty) ->
      let fst' = check_ty genv ctx fst_ty in
      let fst_val = eval_ty (Context.env ctx) fst' in
      let rec bind_all ctx = function
        | [] -> check_ty genv ctx snd_ty
        | name :: rest ->
            let ctx' = Context.bind name fst_val ctx in
            let snd' = bind_all ctx' rest in
            TySigma (name, fst', snd')
      in
      bind_all ctx names
  | Raw.Prod (fst_ty, snd_ty) ->
      let fst' = check_ty genv ctx fst_ty in
      let fst_val = eval_ty (Context.env ctx) fst' in
      let ctx' = Context.bind None fst_val ctx in
      let snd' = check_ty genv ctx' snd_ty in
      TySigma (None, fst', snd')
  | Raw.Int -> TyInt
  | Raw.Eq (a, b) ->
      let a_tm, a_ty = infer_tm genv ctx a in
      let b_tm, _ = infer_tm genv ctx b in
      let a_ty_tm = reify_ty (Context.lvl ctx) a_ty in
      let eq_ty =
        TyEl (TmApp (TmApp (TmApp (TmConst "Eq", a_ty_tm), a_tm), b_tm))
      in
      eq_ty
  | t ->
      let tm, ty_val = infer_tm genv ctx t in
      if not (conv_ty (Context.lvl ctx) ty_val VTyU) then
        raise
          (Elab_error
             (Format.asprintf "Expected Type, got %a" Pretty.pp_ty
                (quote_ty (Context.lvl ctx) ty_val)));
      TyEl tm

and infer_tm (genv : GlobalEnv.t) (ctx : Context.t) : Raw.t -> tm * vl_ty =
  function
  | Raw.Ident name -> (
      match Context.lookup_name ctx name with
      | Some (k, ty) -> (TmVar (Idx k), ty)
      | None -> (
          match GlobalEnv.find_ty genv name with
          | Some ty -> (TmConst name, ty)
          | None ->
              raise (Elab_error (Format.sprintf "Unbound variable: %s" name))))
  | Raw.App (f, a) -> (
      let f', f_ty = infer_tm genv ctx f in
      match f_ty with
      | VTyPi (_, a_ty, ClosTy (env, b_ty)) ->
          let a' = check_tm genv ctx a a_ty in
          let a_val = eval_tm (Context.env ctx) a' in
          (TmApp (f', a'), eval_ty (a_val :: env) b_ty)
      | _ -> raise (Elab_error "Expected function type in application"))
  | Raw.U -> raise (Elab_error "Cannot infer type of Type")
  | Raw.Ann (e, ty) ->
      let ty' = check_ty genv ctx ty in
      let ty_val = eval_ty (Context.env ctx) ty' in
      let e' = check_tm genv ctx e ty_val in
      (e', ty_val)
  | Raw.Lam (binders, body) ->
      let rec go ctx = function
        | [] -> infer_tm genv ctx body
        | (name, Some ty) :: rest ->
            let ty' = check_ty genv ctx ty in
            let ty_val = eval_ty (Context.env ctx) ty' in
            let ctx' = Context.bind name ty_val ctx in
            let body', body_ty = go ctx' rest in
            let clos =
              ClosTy (Context.env ctx, quote_ty (Context.lvl ctx') body_ty)
            in
            (TmLam (name, ty', body'), VTyPi (name, ty_val, clos))
        | (_, None) :: _ ->
            raise (Elab_error "Cannot infer type of lambda without annotation")
      in
      go ctx binders
  | Raw.Pi ((names, dom), cod) ->
      let dom' = infer_tm genv ctx dom in
      let dom_tm, _ = dom' in
      let dom_val = do_el (eval_tm (Context.env ctx) dom_tm) in
      let rec bind_all ctx = function
        | [] ->
            let cod_tm, _ = infer_tm genv ctx cod in
            cod_tm
        | name :: rest ->
            let ctx' = Context.bind name dom_val ctx in
            let cod' = bind_all ctx' rest in
            TmPiHat (name, dom_tm, cod')
      in
      (bind_all ctx names, VTyU)
  | Raw.Arrow (dom, cod) ->
      let dom_tm, _ = infer_tm genv ctx dom in
      let dom_val = do_el (eval_tm (Context.env ctx) dom_tm) in
      let ctx' = Context.bind None dom_val ctx in
      let cod_tm, _ = infer_tm genv ctx' cod in
      (TmPiHat (None, dom_tm, cod_tm), VTyU)
  | Raw.Sigma ((names, fst_ty), snd_ty) ->
      let fst_tm, _ = infer_tm genv ctx fst_ty in
      let fst_val = do_el (eval_tm (Context.env ctx) fst_tm) in
      let rec bind_all ctx = function
        | [] ->
            let snd_tm, _ = infer_tm genv ctx snd_ty in
            snd_tm
        | name :: rest ->
            let ctx' = Context.bind name fst_val ctx in
            let snd' = bind_all ctx' rest in
            TmSigmaHat (name, fst_tm, snd')
      in
      (bind_all ctx names, VTyU)
  | Raw.Prod (fst_ty, snd_ty) ->
      let fst_tm, _ = infer_tm genv ctx fst_ty in
      let fst_val = do_el (eval_tm (Context.env ctx) fst_tm) in
      let ctx' = Context.bind None fst_val ctx in
      let snd_tm, _ = infer_tm genv ctx' snd_ty in
      (TmSigmaHat (None, fst_tm, snd_tm), VTyU)
  | Raw.Pair (a, b) ->
      let a', a_ty = infer_tm genv ctx a in
      let a_val = eval_tm (Context.env ctx) a' in
      let b', b_ty = infer_tm genv ctx b in
      let a_ty_quoted = quote_ty (Context.lvl ctx) a_ty in
      let b_ty_quoted = quote_ty (Context.lvl ctx) b_ty in
      let clos = ClosTy (a_val :: Context.env ctx, b_ty_quoted) in
      (TmMkSigma (a_ty_quoted, b_ty_quoted, a', b'), VTySigma (None, a_ty, clos))
  | Raw.Proj1 t -> (
      let t', t_ty = infer_tm genv ctx t in
      match t_ty with
      | VTySigma (_, fst_ty, _) -> (TmProj1 t', fst_ty)
      | _ -> raise (Elab_error "Expected sigma type in projection"))
  | Raw.Proj2 t -> (
      let t', t_ty = infer_tm genv ctx t in
      match t_ty with
      | VTySigma (_, _, ClosTy (env, snd_ty)) ->
          let fst_val = do_proj1 (eval_tm (Context.env ctx) t') in
          (TmProj2 t', eval_ty (fst_val :: env) snd_ty)
      | _ -> raise (Elab_error "Expected sigma type in projection"))
  | Raw.Int -> (TmIntHat, VTyU)
  | Raw.IntLit n -> (TmIntLit n, VTyInt)
  | Raw.Add (a, b) ->
      let a' = check_tm genv ctx a VTyInt in
      let b' = check_tm genv ctx b VTyInt in
      (TmAdd (a', b'), VTyInt)
  | Raw.Sub (a, b) ->
      let a' = check_tm genv ctx a VTyInt in
      let b' = check_tm genv ctx b VTyInt in
      (TmSub (a', b'), VTyInt)
  | Raw.Eq (a, b) ->
      let a_tm, a_ty = infer_tm genv ctx a in
      let b_tm, _ = infer_tm genv ctx b in
      let a_ty_tm = reify_ty (Context.lvl ctx) a_ty in
      (TmApp (TmApp (TmApp (TmConst "Eq", a_ty_tm), a_tm), b_tm), VTyU)
  | Raw.Let (name, ty_opt, rhs, body) ->
      let rhs', rhs_ty =
        match ty_opt with
        | Some ty ->
            let ty' = check_ty genv ctx ty in
            let ty_val = eval_ty (Context.env ctx) ty' in
            (check_tm genv ctx rhs ty_val, ty_val)
        | None -> infer_tm genv ctx rhs
      in
      let rhs_val = eval_tm (Context.env ctx) rhs' in
      let ctx' = Context.bind (Some name) rhs_ty ctx in
      let env' = rhs_val :: Context.env ctx in
      let body', body_ty = infer_tm genv ctx' body in
      let body_ty_quoted = quote_ty (Context.lvl ctx') body_ty in
      let result_ty = eval_ty env' body_ty_quoted in
      (TmLet (name, quote_ty (Context.lvl ctx) rhs_ty, rhs', body'), result_ty)
  | Raw.Sorry ->
      let id = fresh_sorry_id () in
      let hole_ty = VTyEl (HConst (Format.sprintf "?ty%d†" id), []) in
      (TmSorry (id, quote_ty (Context.lvl ctx) hole_ty), hole_ty)

and check_tm (genv : GlobalEnv.t) (ctx : Context.t) (raw : Raw.t)
    (expected : vl_ty) : tm =
  match (raw, expected) with
  | Raw.Lam (binders, body), _ ->
      let rec go ctx expected = function
        | [] -> check_tm genv ctx body expected
        | (name, ty_opt) :: rest -> (
            match expected with
            | VTyPi (_, a_ty, ClosTy (env, b_ty)) ->
                (match ty_opt with
                | Some ann ->
                    let ann' = check_ty genv ctx ann in
                    let ann_val = eval_ty (Context.env ctx) ann' in
                    if not (conv_ty (Context.lvl ctx) ann_val a_ty) then
                      raise
                        (Elab_error
                           (Format.asprintf
                              "Lambda annotation mismatch: expected %a, got %a"
                              Pretty.pp_ty
                              (quote_ty (Context.lvl ctx) a_ty)
                              Pretty.pp_ty
                              (quote_ty (Context.lvl ctx) ann_val)))
                | None -> ());
                let ctx' = Context.bind name a_ty ctx in
                let var = VTmNeutral (HVar (Lvl (Context.lvl ctx)), []) in
                let b_ty_val = eval_ty (var :: env) b_ty in
                let body' = go ctx' b_ty_val rest in
                TmLam (name, quote_ty (Context.lvl ctx) a_ty, body')
            | _ -> raise (Elab_error "Expected function type for lambda"))
      in
      go ctx expected binders
  | Raw.Pair (a, b), VTySigma (_, fst_ty, ClosTy (env, snd_ty)) ->
      let a' = check_tm genv ctx a fst_ty in
      let a_val = eval_tm (Context.env ctx) a' in
      let snd_ty_val = eval_ty (a_val :: env) snd_ty in
      let b' = check_tm genv ctx b snd_ty_val in
      let fst_ty_quoted = quote_ty (Context.lvl ctx) fst_ty in
      TmMkSigma (fst_ty_quoted, snd_ty, a', b')
  | Raw.Let (name, ty_opt, rhs, body), expected ->
      let rhs', rhs_ty =
        match ty_opt with
        | Some ty ->
            let ty' = check_ty genv ctx ty in
            let ty_val = eval_ty (Context.env ctx) ty' in
            (check_tm genv ctx rhs ty_val, ty_val)
        | None -> infer_tm genv ctx rhs
      in
      let rhs_val = eval_tm (Context.env ctx) rhs' in
      let ctx' = Context.bind (Some name) rhs_ty ctx in
      let env' = rhs_val :: Context.env ctx in
      ignore env';
      let body' = check_tm genv ctx' body expected in
      TmLet (name, quote_ty (Context.lvl ctx) rhs_ty, rhs', body')
  | Raw.Sorry, expected ->
      let id = fresh_sorry_id () in
      TmSorry (id, quote_ty (Context.lvl ctx) expected)
  | _ ->
      let tm, inferred = infer_tm genv ctx raw in
      if not (conv_ty (Context.lvl ctx) inferred expected) then
        raise
          (Elab_error
             (Format.asprintf "Type mismatch: expected %a, got %a" Pretty.pp_ty
                (quote_ty (Context.lvl ctx) expected)
                Pretty.pp_ty
                (quote_ty (Context.lvl ctx) inferred)));
      tm

(* ========== Positivity Checking ========== *)

let rec has_ind_occ_ty (ind : string) : ty -> bool = function
  | TyU
  | TyInt ->
      false
  | TyPi (_, a, b)
  | TySigma (_, a, b) ->
      has_ind_occ_ty ind a || has_ind_occ_ty ind b
  | TyEl t -> has_ind_occ_tm ind t

and has_ind_occ_tm (ind : string) : tm -> bool = function
  | TmVar _ -> false
  | TmConst name -> String.equal name ind
  | TmLam (_, a, body) -> has_ind_occ_ty ind a || has_ind_occ_tm ind body
  | TmApp (f, a) -> has_ind_occ_tm ind f || has_ind_occ_tm ind a
  | TmPiHat (_, a, b)
  | TmSigmaHat (_, a, b) ->
      has_ind_occ_tm ind a || has_ind_occ_tm ind b
  | TmMkSigma (a, b, t, u) ->
      has_ind_occ_ty ind a || has_ind_occ_ty ind b || has_ind_occ_tm ind t
      || has_ind_occ_tm ind u
  | TmProj1 t
  | TmProj2 t ->
      has_ind_occ_tm ind t
  | TmIntLit _
  | TmIntHat ->
      false
  | TmAdd (a, b)
  | TmSub (a, b) ->
      has_ind_occ_tm ind a || has_ind_occ_tm ind b
  | TmSorry (_, ty) -> has_ind_occ_ty ind ty
  | TmLet (_, ty, t, body) ->
      has_ind_occ_ty ind ty || has_ind_occ_tm ind t || has_ind_occ_tm ind body

let is_valid_ind_app (ind : string) : tm -> bool =
  let rec go = function
    | TmConst name -> String.equal name ind
    | TmApp (f, _) -> go f
    | _ -> false
  in
  go

let get_app_head : tm -> string option =
  let rec go = function
    | TmConst name -> Some name
    | TmApp (f, _) -> go f
    | _ -> None
  in
  go

let rec has_var_ty (var_idx : int) : ty -> bool = function
  | TyU
  | TyInt ->
      false
  | TyPi (_, a, b)
  | TySigma (_, a, b) ->
      has_var_ty var_idx a || has_var_ty (var_idx + 1) b
  | TyEl t -> has_var_tm var_idx t

and has_var_tm (var_idx : int) : tm -> bool = function
  | TmVar (Idx i) -> i = var_idx
  | TmConst _ -> false
  | TmLam (_, a, body) -> has_var_ty var_idx a || has_var_tm (var_idx + 1) body
  | TmApp (f, a) -> has_var_tm var_idx f || has_var_tm var_idx a
  | TmPiHat (_, a, b)
  | TmSigmaHat (_, a, b) ->
      has_var_tm var_idx a || has_var_tm (var_idx + 1) b
  | TmMkSigma (a, b, t, u) ->
      has_var_ty var_idx a
      || has_var_ty (var_idx + 1) b
      || has_var_tm var_idx t || has_var_tm var_idx u
  | TmProj1 t
  | TmProj2 t ->
      has_var_tm var_idx t
  | TmIntLit _
  | TmIntHat ->
      false
  | TmAdd (a, b)
  | TmSub (a, b) ->
      has_var_tm var_idx a || has_var_tm var_idx b
  | TmSorry (_, ty) -> has_var_ty var_idx ty
  | TmLet (_, ty, t, body) ->
      has_var_ty var_idx ty || has_var_tm var_idx t
      || has_var_tm (var_idx + 1) body

(* Check if var appears negatively (on the left of an arrow) *)
let rec var_occurs_negatively_ty (var_idx : int) : ty -> bool = function
  | TyU
  | TyInt ->
      false
  | TyPi (_, a, b) ->
      has_var_ty var_idx a || var_occurs_negatively_ty (var_idx + 1) b
  | TySigma (_, a, b) ->
      var_occurs_negatively_ty var_idx a
      || var_occurs_negatively_ty (var_idx + 1) b
  | TyEl t -> var_occurs_negatively_tm var_idx t

and var_occurs_negatively_tm (var_idx : int) : tm -> bool = function
  | TmVar _
  | TmConst _ ->
      false
  | TmLam (_, a, body) ->
      var_occurs_negatively_ty var_idx a
      || var_occurs_negatively_tm (var_idx + 1) body
  | TmApp (f, a) ->
      var_occurs_negatively_tm var_idx f || var_occurs_negatively_tm var_idx a
  | TmPiHat (_, a, b) ->
      has_var_tm var_idx a || var_occurs_negatively_tm (var_idx + 1) b
  | TmSigmaHat (_, a, b) ->
      var_occurs_negatively_tm var_idx a
      || var_occurs_negatively_tm (var_idx + 1) b
  | TmMkSigma (a, b, t, u) ->
      var_occurs_negatively_ty var_idx a
      || var_occurs_negatively_ty (var_idx + 1) b
      || var_occurs_negatively_tm var_idx t
      || var_occurs_negatively_tm var_idx u
  | TmProj1 t
  | TmProj2 t ->
      var_occurs_negatively_tm var_idx t
  | TmIntLit _
  | TmIntHat ->
      false
  | TmAdd (a, b)
  | TmSub (a, b) ->
      var_occurs_negatively_tm var_idx a || var_occurs_negatively_tm var_idx b
  | TmSorry (_, ty) -> var_occurs_negatively_ty var_idx ty
  | TmLet (_, ty, t, body) ->
      var_occurs_negatively_ty var_idx ty
      || var_occurs_negatively_tm var_idx t
      || var_occurs_negatively_tm (var_idx + 1) body

(* Check if inductive F is strictly positive in its first parameter *)
let check_inductive_param_positive (genv : GlobalEnv.t) (f_name : string) : bool
    =
  match GlobalEnv.find_inductive genv f_name with
  | None -> false
  | Some info ->
      let rec count_params = function
        | TyPi (_, _, b) -> 1 + count_params b
        | _ -> 0
      in
      let n_params = count_params info.ind_ty in
      if n_params = 0 then
        true
      else
        let check_ctor_positive (_ctor_name, ctor_ty) =
          let rec skip_and_check skip depth ty =
            match ty with
            | TyPi (_, a, b) ->
                if skip > 0 then
                  skip_and_check (skip - 1) (depth + 1) b
                else
                  let param_var = depth - n_params in
                  if var_occurs_negatively_ty param_var a then
                    false
                  else
                    skip_and_check 0 (depth + 1) b
            | _ -> true
          in
          skip_and_check n_params 0 ctor_ty
        in
        List.for_all check_ctor_positive info.ctors

let rec check_positivity_ty (genv : GlobalEnv.t) (ind : string) (ty : ty) : unit
    =
  if not (has_ind_occ_ty ind ty) then
    ()
  else
    match
      ty
    with
    | TyU
    | TyInt ->
        ()
    | TyPi (_, a, b) ->
        if has_ind_occ_ty ind a then
          raise
            (Elab_error
               (Format.sprintf "%s has a non-positive occurrence (in domain)"
                  ind));
        check_positivity_ty genv ind b
    | TySigma (_, a, b) ->
        check_positivity_ty genv ind a;
        check_positivity_ty genv ind b
    | TyEl t -> check_positivity_tm genv ind t

and check_positivity_tm (genv : GlobalEnv.t) (ind : string) (tm : tm) : unit =
  if not (has_ind_occ_tm ind tm) then
    ()
  else if is_valid_ind_app ind tm then
    ()
  else
    match
      tm
    with
    | TmVar _ -> ()
    | TmConst _ -> ()
    | TmPiHat (_, a, b) ->
        if has_ind_occ_tm ind a then
          raise
            (Elab_error
               (Format.sprintf "%s has a non-positive occurrence (in domain)"
                  ind));
        check_positivity_tm genv ind b
    | TmSigmaHat (_, a, b) ->
        check_positivity_tm genv ind a;
        check_positivity_tm genv ind b
    | TmApp (_, _) -> (
        match get_app_head tm with
        | Some f_name when GlobalEnv.is_inductive genv f_name ->
            if check_inductive_param_positive genv f_name then
              ()
            else
              raise
                (Elab_error
                   (Format.sprintf
                      "%s has a non-positive occurrence (nested in %s)" ind
                      f_name))
        | _ ->
            raise
              (Elab_error
                 (Format.sprintf "%s has a non-valid occurrence (nested)" ind)))
    | TmLam (_, a, body) ->
        check_positivity_ty genv ind a;
        check_positivity_tm genv ind body
    | _ ->
        raise (Elab_error (Format.sprintf "%s has a non-valid occurrence" ind))

let rec check_strict_positivity (genv : GlobalEnv.t) (ind : string) : ty -> unit
    = function
  | TyPi (_, a, b) ->
      check_positivity_ty genv ind a;
      check_strict_positivity genv ind b
  | _ -> ()

let rec check_returns_inductive (ind : string) : ty -> bool = function
  | TyEl (TmConst name) -> String.equal name ind
  | TyEl (TmApp (f, _)) -> check_returns_inductive_tm ind f
  | TyPi (_, _, b) -> check_returns_inductive ind b
  | _ -> false

and check_returns_inductive_tm (ind : string) : tm -> bool = function
  | TmConst name -> String.equal name ind
  | TmApp (f, _) -> check_returns_inductive_tm ind f
  | _ -> false

let check_return_params (ctor_name : string) (ind : string) (num_params : int)
    (ty : ty) : unit =
  let rec get_return_head = function
    | TyPi (_, _, b) -> get_return_head b
    | TyEl t -> Some t
    | _ -> None
  in
  match get_return_head ty with
  | None -> ()
  | Some ret_tm ->
      let rec get_app_args acc = function
        | TmApp (f, a) -> get_app_args (a :: acc) f
        | t -> (t, acc)
      in
      let head, args = get_app_args [] ret_tm in
      if head <> TmConst ind then
        ()
      else if List.length args < num_params then
        raise
          (Elab_error
             (Format.sprintf "%s: return type must apply %s to all parameters"
                ctor_name ind))

(* ========== Inductive Types ========== *)

let elab_ctor (genv : GlobalEnv.t) (ind : string) (param_ctx : Context.t)
    (param_tys : (string option * ty) list) (num_params : int)
    ((ctor_name, ctor_params, ctor_ty_opt) : Raw.ctor) : string * ty * vl_ty =
  let full_name = Format.sprintf "%s.%s" ind ctor_name in
  let rec build_ctor_body ctx = function
    | [] -> (
        match ctor_ty_opt with
        | None ->
            let base = TmConst ind in
            let applied =
              List.fold_left
                (fun acc i -> TmApp (acc, TmVar (Idx (num_params - 1 - i))))
                base
                (List.init num_params (fun i -> i))
            in
            TyEl applied
        | Some ret_raw ->
            let ret_ty = check_ty genv ctx ret_raw in
            if not (check_returns_inductive ind ret_ty) then
              raise
                (Elab_error (Format.sprintf "%s must return %s" full_name ind));
            check_return_params full_name ind num_params ret_ty;
            ret_ty)
    | (name, ty_opt) :: rest ->
        let param_ty =
          match ty_opt with
          | Some ty_raw -> check_ty genv ctx ty_raw
          | None ->
              raise
                (Elab_error
                   (Format.sprintf "%s: parameter needs type" full_name))
        in
        let param_ty_val = eval_ty (Context.env ctx) param_ty in
        let ctx' = Context.bind name param_ty_val ctx in
        let body_ty = build_ctor_body ctx' rest in
        TyPi (name, param_ty, body_ty)
  in
  let ctor_body = build_ctor_body param_ctx ctor_params in
  let ctor_ty =
    List.fold_right
      (fun (name, ty) body -> TyPi (name, ty, body))
      param_tys ctor_body
  in
  check_strict_positivity genv ind ctor_ty;
  let ctor_ty_val = eval_ty [] ctor_ty in
  (full_name, ctor_ty, ctor_ty_val)

(* ========== Recursor Generation ========== *)

let rec is_recursive_arg_ty (ind : string) : ty -> bool = function
  | TyEl (TmConst name) -> String.equal name ind
  | TyEl (TmApp (f, _)) -> is_recursive_arg_tm ind f
  | TyPi (_, _, b) -> is_recursive_arg_ty ind b
  | _ -> false

and is_recursive_arg_tm (ind : string) : tm -> bool = function
  | TmConst name -> String.equal name ind
  | TmApp (f, _) -> is_recursive_arg_tm ind f
  | _ -> false

let rec shift_ty (amt : int) (cutoff : int) : ty -> ty = function
  | TyU -> TyU
  | TyInt -> TyInt
  | TyPi (x, a, b) ->
      TyPi (x, shift_ty amt cutoff a, shift_ty amt (cutoff + 1) b)
  | TySigma (x, a, b) ->
      TySigma (x, shift_ty amt cutoff a, shift_ty amt (cutoff + 1) b)
  | TyEl t -> TyEl (shift_tm amt cutoff t)

and shift_tm (amt : int) (cutoff : int) : tm -> tm = function
  | TmVar (Idx i) ->
      TmVar
        (Idx
           (if i >= cutoff then
              i + amt
            else
              i))
  | TmConst name -> TmConst name
  | TmLam (x, a, body) ->
      TmLam (x, shift_ty amt cutoff a, shift_tm amt (cutoff + 1) body)
  | TmApp (f, a) -> TmApp (shift_tm amt cutoff f, shift_tm amt cutoff a)
  | TmPiHat (x, a, b) ->
      TmPiHat (x, shift_tm amt cutoff a, shift_tm amt (cutoff + 1) b)
  | TmSigmaHat (x, a, b) ->
      TmSigmaHat (x, shift_tm amt cutoff a, shift_tm amt (cutoff + 1) b)
  | TmMkSigma (a, b, t, u) ->
      TmMkSigma
        ( shift_ty amt cutoff a,
          shift_ty amt (cutoff + 1) b,
          shift_tm amt cutoff t,
          shift_tm amt cutoff u )
  | TmProj1 t -> TmProj1 (shift_tm amt cutoff t)
  | TmProj2 t -> TmProj2 (shift_tm amt cutoff t)
  | TmIntLit i -> TmIntLit i
  | TmIntHat -> TmIntHat
  | TmAdd (a, b) -> TmAdd (shift_tm amt cutoff a, shift_tm amt cutoff b)
  | TmSub (a, b) -> TmSub (shift_tm amt cutoff a, shift_tm amt cutoff b)
  | TmSorry (id, ty) -> TmSorry (id, shift_ty amt cutoff ty)
  | TmLet (x, ty, t, body) ->
      TmLet
        ( x,
          shift_ty amt cutoff ty,
          shift_tm amt cutoff t,
          shift_tm amt (cutoff + 1) body )

let rec extract_indices : ty -> (string option * ty) list = function
  | TyPi (name, a, b) -> (name, a) :: extract_indices b
  | TyU -> []
  | _ -> []

let rec extract_return_indices_from_ctor (ind : string) (num_params : int) :
    ty -> tm list = function
  | TyPi (_, _, b) -> extract_return_indices_from_ctor ind num_params b
  | TyEl tm -> extract_args_after_params ind num_params tm
  | _ -> []

and extract_args_after_params (ind : string) (num_params : int) (tm : tm) :
    tm list =
  let rec collect_all_args tm acc =
    match tm with
    | TmConst name when String.equal name ind -> acc
    | TmApp (f, a) -> collect_all_args f (a :: acc)
    | _ -> []
  in
  let all_args = collect_all_args tm [] in
  if List.length all_args >= num_params then
    List.filteri (fun i _ -> i >= num_params) all_args
  else
    []

let extract_nested_rec_info (ind : string) (num_params : int) (ty : ty) :
    (string option * ty) list * tm list =
  let rec go acc ty =
    match ty with
    | TyPi (name, arg_ty, body) -> go ((name, arg_ty) :: acc) body
    | TyEl tm ->
        let indices = extract_args_after_params ind num_params tm in
        (List.rev acc, indices)
    | _ -> (List.rev acc, [])
  in
  go [] ty

let count_ctor_fields (num_params : int) (ctor_ty : ty) : int =
  let rec strip n ty =
    if n = 0 then
      ty
    else
      match
        ty
      with
      | TyPi (_, _, b) -> strip (n - 1) b
      | _ -> ty
  in
  let rec count = function
    | TyPi (_, _, b) -> 1 + count b
    | _ -> 0
  in
  count (strip num_params ctor_ty)

let get_ctor_field_types (num_params : int) (ctor_ty : ty) :
    (string option * ty) list =
  let rec strip n ty =
    if n = 0 then
      ty
    else
      match
        ty
      with
      | TyPi (_, _, b) -> strip (n - 1) b
      | _ -> ty
  in
  let rec collect = function
    | TyPi (name, a, b) -> (name, a) :: collect b
    | _ -> []
  in
  collect (strip num_params ctor_ty)

(* Generate recursor type for an inductive *)
let gen_recursor_ty (ind : string) (num_params : int)
    (param_tys : (string option * ty) list)
    (index_tys : (string option * ty) list) (ctor_tys : (string * ty) list) : ty
    =
  let num_indices = List.length index_tys in
  let num_ctors = List.length ctor_tys in

  (* Binding depths *)
  let motive_depth = num_params in
  let method_depth i = num_params + 1 + i in
  let target_idx_depth i = num_params + 1 + num_ctors + i in
  let major_depth = num_params + 1 + num_ctors + num_indices in
  let result_depth = major_depth + 1 in

  let idx_of d v = v - d - 1 in

  let build_ind_app ~view_depth ~index_terms =
    let base = TmConst ind in
    let with_params =
      let rec apply i acc =
        if i >= num_params then
          acc
        else
          apply (i + 1) (TmApp (acc, TmVar (Idx (idx_of i view_depth))))
      in
      apply 0 base
    in
    List.fold_left (fun acc t -> TmApp (acc, t)) with_params index_terms
  in

  (* Motive: (indices...) -> (x : Ind params indices) -> Type *)
  let motive_ty =
    let body = TyU in
    let x_view_depth = motive_depth + num_indices in
    let index_terms =
      List.init num_indices (fun i ->
          TmVar (Idx (idx_of (motive_depth + i) x_view_depth)))
    in
    let x_type = TyEl (build_ind_app ~view_depth:x_view_depth ~index_terms) in
    let with_x = TyPi (Some "x", x_type, body) in
    let rec add_index_binders i acc =
      if i < 0 then
        acc
      else
        let name, idx_ty = List.nth index_tys i in
        let name' =
          match name with
          | Some n -> Some n
          | None -> Some ("a" ^ string_of_int i)
        in
        add_index_binders (i - 1) (TyPi (name', idx_ty, acc))
    in
    add_index_binders (num_indices - 1) with_x
  in

  (* Method types *)
  let strip_params ty =
    let rec go n t =
      if n = 0 then
        t
      else
        match
          t
        with
        | TyPi (_, _, b) -> go (n - 1) b
        | _ -> t
    in
    go num_params ty
  in

  let gen_method_ty (_ctor_name : string) (ctor_ty : ty) (ctor_idx : int) : ty =
    let my_depth = method_depth ctor_idx in
    let fields_ty = strip_params ctor_ty in

    let rec collect_fields ty field_num =
      match ty with
      | TyPi (name, arg_ty, rest) ->
          let is_rec = is_recursive_arg_ty ind arg_ty in
          (name, arg_ty, is_rec, field_num)
          :: collect_fields rest (field_num + 1)
      | _ -> []
    in
    let all_fields = collect_fields fields_ty 0 in
    let num_fields = List.length all_fields in
    let num_ihs =
      List.length (List.filter (fun (_, _, is_rec, _) -> is_rec) all_fields)
    in
    let total_inner_binders = num_fields + num_ihs in
    let return_indices =
      extract_return_indices_from_ctor ind num_params ctor_ty
    in
    let inner_depth = my_depth + total_inner_binders in

    let field_bind_depths =
      let rec compute field_idx ih_count acc = function
        | [] -> List.rev acc
        | (_, _, is_rec, field_num) :: rest ->
            let depth = my_depth + field_idx + ih_count in
            let new_ih =
              if is_rec then
                ih_count + 1
              else
                ih_count
            in
            compute (field_idx + 1) new_ih ((field_num, depth) :: acc) rest
      in
      compute 0 0 [] all_fields
    in

    let subst_tm tm =
      let param_idxs = List.init num_params (fun i -> idx_of i inner_depth) in
      let rec go = function
        | TmVar (Idx i) ->
            if i < num_fields then
              let field_num = num_fields - 1 - i in
              let _, d =
                List.find (fun (j, _) -> j = field_num) field_bind_depths
              in
              TmVar (Idx (idx_of d inner_depth))
            else
              let param_num = num_params - 1 - (i - num_fields) in
              if param_num >= 0 && param_num < num_params then
                TmVar (Idx (List.nth param_idxs param_num))
              else
                TmVar (Idx i)
        | TmApp (f, a) -> TmApp (go f, go a)
        | TmConst n -> TmConst n
        | t -> t
      in
      go tm
    in

    let mapped_indices = List.map subst_tm return_indices in

    let ctor_app =
      let base = TmConst _ctor_name in
      let param_idxs = List.init num_params (fun i -> idx_of i inner_depth) in
      let with_params =
        List.fold_left (fun acc i -> TmApp (acc, TmVar (Idx i))) base param_idxs
      in
      List.fold_left
        (fun acc (_, _, _, field_num) ->
          let _, d =
            List.find (fun (j, _) -> j = field_num) field_bind_depths
          in
          TmApp (acc, TmVar (Idx (idx_of d inner_depth))))
        with_params all_fields
    in

    let motive_idx = idx_of motive_depth inner_depth in
    let motive_applied =
      List.fold_left
        (fun acc t -> TmApp (acc, t))
        (TmVar (Idx motive_idx)) mapped_indices
    in
    let result = TyEl (TmApp (motive_applied, ctor_app)) in

    let subst_field_ty field_num view_depth =
      let rec subst_tm_inner extra_binders = function
        | TmVar (Idx i) ->
            if i < extra_binders then
              TmVar (Idx i)
            else
              let orig_i = i - extra_binders in
              if orig_i < field_num then
                let j = field_num - 1 - orig_i in
                let _, bind_d =
                  List.find (fun (k, _) -> k = j) field_bind_depths
                in
                TmVar (Idx (idx_of bind_d (view_depth + extra_binders)))
              else
                let ctor_param_offset = orig_i - field_num in
                let actual_param = num_params - 1 - ctor_param_offset in
                TmVar (Idx (idx_of actual_param (view_depth + extra_binders)))
        | TmApp (f, a) ->
            TmApp
              (subst_tm_inner extra_binders f, subst_tm_inner extra_binders a)
        | TmConst n -> TmConst n
        | t -> t
      in
      let rec subst_ty_inner extra_binders = function
        | TyU -> TyU
        | TyInt -> TyInt
        | TyPi (x, a, b) ->
            TyPi
              ( x,
                subst_ty_inner extra_binders a,
                subst_ty_inner (extra_binders + 1) b )
        | TySigma (x, a, b) ->
            TySigma
              ( x,
                subst_ty_inner extra_binders a,
                subst_ty_inner (extra_binders + 1) b )
        | TyEl t -> TyEl (subst_tm_inner extra_binders t)
      in
      subst_ty_inner 0
    in

    let build_ih_type nested_binders rec_indices motive_idx field_var_idx =
      let num_nested = List.length nested_binders in
      if num_nested = 0 then
        let shifted_indices = List.map (shift_tm 1 0) rec_indices in
        let motive_app =
          List.fold_left
            (fun acc t -> TmApp (acc, t))
            (TmVar (Idx motive_idx)) shifted_indices
        in
        TyEl (TmApp (motive_app, TmVar (Idx field_var_idx)))
      else
        let field_idx = field_var_idx + num_nested in
        let motive_final_idx = motive_idx + num_nested in
        let field_app =
          let field_tm = TmVar (Idx field_idx) in
          List.fold_left
            (fun acc i -> TmApp (acc, TmVar (Idx (num_nested - 1 - i))))
            field_tm
            (List.init num_nested (fun i -> i))
        in
        let motive_app =
          List.fold_left
            (fun acc t -> TmApp (acc, t))
            (TmVar (Idx motive_final_idx)) rec_indices
        in
        let ih_body = TyEl (TmApp (motive_app, field_app)) in
        let rev_binders = List.rev nested_binders in
        let ih_ty =
          List.fold_left
            (fun (depth_from_inner, acc) (name, ty) ->
              let name' =
                match name with
                | Some n -> Some n
                | None -> Some (Format.sprintf "a%d†" depth_from_inner)
              in
              let orig_depth = num_nested - 1 - depth_from_inner in
              let shifted_ty = shift_ty 1 orig_depth ty in
              (depth_from_inner + 1, TyPi (name', shifted_ty, acc)))
            (0, ih_body) rev_binders
        in
        snd ih_ty
    in

    let rec build_pis remaining_fields ih_count acc =
      match remaining_fields with
      | [] -> acc
      | (name, field_ty, is_rec, field_num) :: rest ->
          let _, field_depth =
            List.find (fun (i, _) -> i = field_num) field_bind_depths
          in
          let subst_ty = subst_field_ty field_num field_depth in
          let substituted_ty = subst_ty field_ty in
          if is_rec then
            let nested_binders, rec_indices =
              extract_nested_rec_info ind num_params substituted_ty
            in
            let ih_depth = field_depth + 1 in
            let ih_motive_idx = idx_of motive_depth ih_depth in
            let field_var_idx = idx_of field_depth ih_depth in
            let ih_ty =
              build_ih_type nested_binders rec_indices ih_motive_idx
                field_var_idx
            in
            let ih_name =
              Some (Format.sprintf "%s_ih" (Option.value name ~default:"x"))
            in
            let with_ih = TyPi (ih_name, ih_ty, acc) in
            build_pis rest (ih_count + 1) (TyPi (name, substituted_ty, with_ih))
          else
            build_pis rest ih_count (TyPi (name, substituted_ty, acc))
    in
    build_pis (List.rev all_fields) 0 result
  in

  let methods = List.mapi (fun i (n, t) -> gen_method_ty n t i) ctor_tys in

  (* Target: (indices...) -> (x : Ind params indices) -> motive indices x *)
  let target_ty =
    let index_idxs =
      List.init num_indices (fun i -> idx_of (target_idx_depth i) result_depth)
    in
    let motive_idx = idx_of motive_depth result_depth in
    let motive_app =
      List.fold_left
        (fun acc i -> TmApp (acc, TmVar (Idx i)))
        (TmVar (Idx motive_idx)) index_idxs
    in
    let result = TyEl (TmApp (motive_app, TmVar (Idx 0))) in
    let x_index_terms =
      List.init num_indices (fun i ->
          TmVar (Idx (idx_of (target_idx_depth i) major_depth)))
    in
    let x_type =
      TyEl (build_ind_app ~view_depth:major_depth ~index_terms:x_index_terms)
    in
    let with_x = TyPi (Some "x", x_type, result) in
    let rec add_idx_binders i acc =
      if i < 0 then
        acc
      else
        let name, idx_ty = List.nth index_tys i in
        let name' =
          match name with
          | Some n -> Some n
          | None -> Some (Format.sprintf "a%d†" i)
        in
        let shift = 1 + num_ctors in
        let shifted_ty = shift_ty shift i idx_ty in
        add_idx_binders (i - 1) (TyPi (name', shifted_ty, acc))
    in
    add_idx_binders (num_indices - 1) with_x
  in

  let with_methods =
    List.fold_right (fun m acc -> TyPi (None, m, acc)) methods target_ty
  in
  let with_motive = TyPi (Some "motive", motive_ty, with_methods) in
  List.fold_right
    (fun (name, ty) acc -> TyPi (name, ty, acc))
    param_tys with_motive

let elab_inductive (genv : GlobalEnv.t) (ind : string)
    (raw_params : Raw.binder_group list) (ind_ty_opt : Raw.t option)
    (ctors : Raw.ctor list) : (string * ty) list =
  let rec elab_params ctx acc_tys = function
    | [] -> (ctx, List.rev acc_tys)
    | (names, ty_raw) :: rest ->
        let param_ty = check_ty genv ctx ty_raw in
        let param_ty_val = eval_ty (Context.env ctx) param_ty in
        let ctx', tys =
          List.fold_left
            (fun (c, ts) name ->
              (Context.bind name param_ty_val c, (name, param_ty) :: ts))
            (ctx, acc_tys) names
        in
        elab_params ctx' tys rest
  in
  let param_ctx, param_tys = elab_params Context.empty [] raw_params in
  let num_params = List.length param_tys in
  let result_ty =
    match ind_ty_opt with
    | None -> TyU
    | Some ty_raw -> check_ty genv param_ctx ty_raw
  in
  let ind_ty =
    List.fold_right
      (fun (name, ty) body -> TyPi (name, ty, body))
      param_tys result_ty
  in
  let ind_ty_val = eval_ty [] ind_ty in
  GlobalEnv.add_opaque genv ind ind_ty_val;
  let ctor_results =
    List.map (elab_ctor genv ind param_ctx param_tys num_params) ctors
  in
  List.iter
    (fun (name, _ty, ty_val) -> GlobalEnv.add_opaque genv name ty_val)
    ctor_results;
  let ctor_name_tys = List.map (fun (name, ty, _) -> (name, ty)) ctor_results in
  GlobalEnv.add_inductive genv ind ind_ty ctor_name_tys;
  let rec_name = Format.sprintf "%s.rec" ind in
  let index_tys = extract_indices result_ty in
  let rec_ty =
    gen_recursor_ty ind num_params param_tys index_tys ctor_name_tys
  in
  let rec_ty_val = eval_ty [] rec_ty in
  GlobalEnv.add_opaque genv rec_name rec_ty_val;
  ((ind, ind_ty) :: ctor_name_tys) @ [ (rec_name, rec_ty) ]

(* ========== Program Elaboration ========== *)

exception Circular_import of string
exception Import_not_found of string

let module_to_path (root : string) (module_name : string) : string =
  let parts = String.split_on_char '.' module_name in
  let path = String.concat "/" parts in
  Filename.concat root (path ^ ".qdt")

type elab_state = {
  genv : GlobalEnv.t;
  mutable importing : string list;
      (* stack of modules currently being imported *)
  imported : (string, unit) Hashtbl.t; (* already imported modules *)
}

let elab_program_with_imports ~(root : string) ~(read_file : string -> string)
    ~(parse : string -> Raw.program) (prog : Raw.program) :
    (string * tm * ty) list =
  let state =
    { genv = GlobalEnv.create (); importing = []; imported = Hashtbl.create 16 }
  in
  current_genv := GlobalEnv.find_tm state.genv;

  let rec process_import module_name =
    if List.mem module_name state.importing then
      raise (Circular_import module_name);
    if Hashtbl.mem state.imported module_name then
      ()
    else
      let path = module_to_path root module_name in
      let content =
        try read_file path with
        | _ -> raise (Import_not_found module_name)
      in
      let imported_prog = parse content in
      state.importing <- module_name :: state.importing;
      ignore (go [] Context.empty imported_prog);
      state.importing <- List.tl state.importing;
      Hashtbl.add state.imported module_name ()
  and go acc ctx = function
    | [] -> List.rev acc
    | Raw.Import module_name :: rest ->
        process_import module_name;
        go acc ctx rest
    | Raw.Def (name, body) :: rest ->
        let term, ty_val = infer_tm state.genv ctx body in
        let term_val = eval_tm (Context.env ctx) term in
        GlobalEnv.add state.genv name ty_val term_val;
        let ty_out = quote_ty 0 ty_val in
        go ((name, term, ty_out) :: acc) ctx rest
    | Raw.Example body :: rest ->
        let _term, _ty_val = infer_tm state.genv ctx body in
        go acc ctx rest
    | Raw.Inductive (name, params, ty_opt, ctors) :: rest ->
        let results = elab_inductive state.genv name params ty_opt ctors in
        let new_acc =
          List.fold_left
            (fun acc (n, ty) -> (n, TmConst n, ty) :: acc)
            acc results
        in
        go new_acc ctx rest
  in
  go [] Context.empty prog

let elab_program (prog : Raw.program) : (string * tm * ty) list =
  elab_program_with_imports ~root:"."
    ~read_file:(fun _ -> "")
    ~parse:(fun _ -> [])
    prog
