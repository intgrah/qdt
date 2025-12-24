open Frontend
open Syntax
open Nbe

exception Elab_error of string

let fresh_sorry_id =
  let counter = ref 0 in
  fun () ->
    let id = !counter in
    incr counter;
    id

(* ========== Quoting ========== *)

let rec quote_ty (genv : Global.t) (l : int) : vl_ty -> ty = function
  | VTyU -> TyU
  | VTyPi (x, a, ClosTy (env, body)) ->
      let a' = quote_ty genv l a in
      let var = VTmNeutral (HVar (Lvl l), []) in
      let b' = quote_ty genv (l + 1) (eval_ty genv (var :: env) body) in
      TyPi (x, a', b')
  | VTyEl n -> TyEl (quote_neutral genv l n)

and quote_tm (genv : Global.t) (l : int) : vl_tm -> tm = function
  | VTmNeutral n -> quote_neutral genv l n
  | VTmLam (x, a, ClosTm (env, body)) ->
      let var = VTmNeutral (HVar (Lvl l), []) in
      let a = quote_ty genv l a in
      let body' = quote_tm genv (l + 1) (eval_tm genv (var :: env) body) in
      TmLam (x, a, body')
  | VTmPiHat (x, a, ClosTm (env, body)) ->
      let a = quote_tm genv l a in
      let var = VTmNeutral (HVar (Lvl l), []) in
      let b = quote_tm genv (l + 1) (eval_tm genv (var :: env) body) in
      TmPiHat (x, a, b)

and quote_neutral (genv : Global.t) (l : int) ((head, sp) : neutral) : tm =
  let head =
    match head with
    | HVar (Lvl k) -> TmVar (Idx (l - k - 1))
    | HConst name -> TmConst name
    | HSorry (id, ty) -> TmSorry (id, quote_ty genv l ty)
  in
  List.fold_left (fun head arg -> TmApp (head, quote_tm genv l arg)) head sp

(* Convert a value type to a term representing its code *)
and reify_ty (genv : Global.t) (l : int) : vl_ty -> tm = function
  | VTyU -> raise (Elab_error "Cannot reify Type as a term")
  | VTyPi (x, a, ClosTy (env, b)) ->
      let var = VTmNeutral (HVar (Lvl l), []) in
      let a' = reify_ty genv l a in
      let b_ty = eval_ty genv (var :: env) b in
      let b' = reify_ty genv (l + 1) b_ty in
      TmPiHat (x, a', b')
  | VTyEl n -> quote_neutral genv l n

(* ========== Conversion ========== *)

let rec conv_ty (genv : Global.t) (l : int) (ty1 : vl_ty) (ty2 : vl_ty) : bool =
  match (ty1, ty2) with
  | VTyU, VTyU -> true
  | VTyPi (_, a1, ClosTy (env1, b1)), VTyPi (_, a2, ClosTy (env2, b2)) ->
      conv_ty genv l a1 a2
      &&
      let var = VTmNeutral (HVar (Lvl l), []) in
      conv_ty genv (l + 1)
        (eval_ty genv (var :: env1) b1)
        (eval_ty genv (var :: env2) b2)
  | VTyEl n1, VTyEl n2 -> conv_neutral genv l (n1, n2)
  | _ -> false

and conv_tm (genv : Global.t) (l : int) (tm1 : vl_tm) (tm2 : vl_tm) : bool =
  match (tm1, tm2) with
  | VTmNeutral n1, VTmNeutral n2 ->
      conv_neutral genv l (n1, n2)
      || try_eta_struct genv l n1 (VTmNeutral n1)
      || try_eta_struct genv l n2 (VTmNeutral n2)
  | VTmLam (_, _, ClosTm (env1, body1)), VTmLam (_, _, ClosTm (env2, body2)) ->
      let var = VTmNeutral (HVar (Lvl l), []) in
      conv_tm genv (l + 1)
        (eval_tm genv (var :: env1) body1)
        (eval_tm genv (var :: env2) body2)
  | VTmPiHat (_, a1, ClosTm (env1, b1)), VTmPiHat (_, a2, ClosTm (env2, b2)) ->
      conv_tm genv l a1 a2
      &&
      let var = VTmNeutral (HVar (Lvl l), []) in
      conv_tm genv (l + 1)
        (eval_tm genv (var :: env1) b1)
        (eval_tm genv (var :: env2) b2)
  | _ -> false

and try_eta_struct (genv : Global.t) (l : int) (ctor_app : neutral)
    (other : vl_tm) : bool =
  match ctor_app with
  | HConst ctor_name, sp -> (
      match Global.find_constructor ctor_name genv with
      | None -> false
      | Some info -> (
          let info_opt : Global.structure_info option =
            match Global.find_structure info.ind_name genv with
            | Some info -> Some info
            | None -> (
                (* Also allow eta for unit-like types *)
                match
                  Global.find_recursor (Name.child info.ind_name "rec") genv
                with
                | Some rec_info
                  when rec_info.rec_num_indices = 0
                       && List.length rec_info.rec_rules = 1 ->
                    let rule = List.hd rec_info.rec_rules in
                    if
                      rule.rule_rec_args = [] && rule.rule_nfields = 0
                      && rule.rule_ctor_name = ctor_name
                    then
                      Some
                        {
                          struct_ind_name = info.ind_name;
                          struct_ctor_name = ctor_name;
                          struct_num_params = rec_info.rec_num_params;
                          struct_num_fields = 0;
                          struct_field_names = [];
                        }
                    else
                      None
                | _ -> None)
          in
          match info_opt with
          | None -> false
          | Some info ->
              if
                List.length sp
                <> info.struct_num_params + info.struct_num_fields
              then
                false
              else
                let params = List.take info.struct_num_params sp in
                let fields = List.drop info.struct_num_params sp in
                let rec check_fields : string list * vl_tm list -> bool =
                  function
                  | [], [] -> true
                  | fname :: fname_rest, field :: field_rest ->
                      let proj_name = Name.child info.struct_ind_name fname in
                      let proj_result =
                        match Global.find_tm proj_name genv with
                        | Some proj_fn ->
                            let with_params =
                              List.fold_left (do_app genv) proj_fn params
                            in
                            do_app genv with_params other
                        | None -> VTmNeutral (HConst proj_name, [])
                      in
                      conv_tm genv l field proj_result
                      && check_fields (fname_rest, field_rest)
                  | _ -> false
                in
                check_fields (info.struct_field_names, fields)))
  | _, _ -> false

and conv_neutral (genv : Global.t) (l : int)
    (((h1, sp1), (h2, sp2)) : neutral * neutral) : bool =
  let head_eq =
    match (h1, h2) with
    | HVar l1, HVar l2 -> l1 = l2
    | HConst n1, HConst n2 -> n1 = n2
    | HSorry (id1, _), HSorry (id2, _) -> id1 = id2
    | _, _ -> false
  in
  head_eq && List.for_all2 (conv_tm genv l) sp1 sp2

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

  let bind_def name ty value ctx =
    {
      entries = { name; ty } :: ctx.entries;
      env = value :: ctx.env;
      lvl = ctx.lvl + 1;
    }

  let lookup_idx ctx (Idx.Idx k) =
    let e = List.nth ctx.entries k in
    e.ty

  let lookup_name ctx name =
    let rec go k = function
      | [] -> None
      | { name = Some n; ty } :: _ when n = name -> Some (k, ty)
      | _ :: rest -> go (k + 1) rest
    in
    go 0 ctx.entries

  let names ctx =
    List.map
      (fun e ->
        match e.name with
        | Some n -> n
        | None -> "_")
      ctx.entries
end

let find_ty (genv : Global.t) (name : Name.t) : vl_ty option =
  match Global.find_opt name genv with
  | Some (Global.Def { ty; _ })
  | Some (Global.Opaque { ty })
  | Some (Global.Recursor { ty; _ })
  | Some (Global.Constructor { ty; _ }) ->
      Some ty
  | Some (Global.Inductive { ty; _ }) -> Some (eval_ty genv [] ty)
  | Some (Global.Structure { ind = { ty; _ }; _ }) -> Some (eval_ty genv [] ty)
  | None -> None

(* ========== Elaboration ========== *)

let rec check_ty (genv : Global.t) (ctx : Context.t) : Raw_syntax.t -> ty =
  function
  | U -> TyU
  | Pi ((names, dom), cod) ->
      let dom = check_ty genv ctx dom in
      let ctx0 = ctx in
      let dom_val0 = eval_ty genv (Context.env ctx0) dom in
      let dom_ty_at (n : int) : ty =
        quote_ty genv (Context.lvl ctx0 + n) dom_val0
      in
      let rec bind_all ctx n = function
        | [] -> check_ty genv ctx cod
        | name :: rest ->
            let ctx' = Context.bind name dom_val0 ctx in
            let cod' = bind_all ctx' (n + 1) rest in
            TyPi (name, dom_ty_at n, cod')
      in
      bind_all ctx0 0 names
  | Arrow (dom, cod) ->
      let dom = check_ty genv ctx dom in
      let dom_val = eval_ty genv (Context.env ctx) dom in
      let ctx = Context.bind None dom_val ctx in
      let cod = check_ty genv ctx cod in
      TyPi (None, dom, cod)
  | Sigma (binders, snd_ty) ->
      check_ty genv ctx (Desugar.desugar_sigma binders snd_ty)
  | Prod (fst_ty, snd_ty) ->
      check_ty genv ctx (Desugar.desugar_prod fst_ty snd_ty)
  | Eq (a, b) ->
      let a_tm, a_ty = infer_tm genv ctx a in
      let b_tm, _ = infer_tm genv ctx b in
      let a_ty_tm = reify_ty genv (Context.lvl ctx) a_ty in
      let eq_ty =
        TyEl (TmApp (TmApp (TmApp (TmConst [ "Eq" ], a_ty_tm), a_tm), b_tm))
      in
      eq_ty
  | t ->
      let tm, ty_val = infer_tm genv ctx t in
      if not (conv_ty genv (Context.lvl ctx) ty_val VTyU) then
        raise
          (Elab_error
             (Format.asprintf "Expected Type, got %a"
                (Pretty.pp_ty_ctx (Context.names ctx))
                (quote_ty genv (Context.lvl ctx) ty_val)));
      TyEl tm

and infer_tm (genv : Global.t) (ctx : Context.t) : Raw_syntax.t -> tm * vl_ty =
  function
  | Ident name -> (
      match Context.lookup_name ctx name with
      | Some (k, ty) -> (TmVar (Idx k), ty)
      | None -> (
          let fqn = Name.parse name in
          match find_ty genv fqn with
          | Some ty -> (TmConst fqn, ty)
          | None ->
              raise (Elab_error (Format.sprintf "Unbound variable: %s" name))))
  | App (f, a) -> (
      let f', f_ty = infer_tm genv ctx f in
      match f_ty with
      | VTyPi (_, a_ty, ClosTy (env, b_ty)) ->
          let a' = check_tm genv ctx a a_ty in
          let a_val = eval_tm genv (Context.env ctx) a' in
          (TmApp (f', a'), eval_ty genv (a_val :: env) b_ty)
      | _ -> raise (Elab_error "Expected function type in application"))
  | U -> raise (Elab_error "Cannot infer type of Type")
  | Ann (e, ty) ->
      let ty = check_ty genv ctx ty in
      let ty_val = eval_ty genv (Context.env ctx) ty in
      let e = check_tm genv ctx e ty_val in
      (e, ty_val)
  | Lam (binders, body) ->
      let flatten_binders (binders : Raw_syntax.binder_group list) :
          (string option * Raw_syntax.t option) list =
        List.concat_map
          (function
            | Raw_syntax.Untyped name -> [ (Some name, None) ]
            | Raw_syntax.Typed (names, ty) ->
                List.map (fun name -> (name, Some ty)) names)
          binders
      in
      let rec go ctx = function
        | [] -> infer_tm genv ctx body
        | (name, Some ty) :: rest ->
            let ty' = check_ty genv ctx ty in
            let ty_val = eval_ty genv (Context.env ctx) ty' in
            let ctx' = Context.bind name ty_val ctx in
            let body', body_ty = go ctx' rest in
            let clos =
              ClosTy (Context.env ctx, quote_ty genv (Context.lvl ctx') body_ty)
            in
            (TmLam (name, ty', body'), VTyPi (name, ty_val, clos))
        | (_, None) :: _ ->
            raise (Elab_error "Cannot infer type of unannotated lambda :(")
      in
      go ctx (flatten_binders binders)
  | Pi ((names, dom), cod) ->
      let dom, _ = infer_tm genv ctx dom in
      let dom_val = do_el (eval_tm genv (Context.env ctx) dom) in
      let dom_tm_at (n : int) : tm =
        reify_ty genv (Context.lvl ctx + n) dom_val
      in
      let rec bind_all ctx n = function
        | [] ->
            let cod_tm, _ = infer_tm genv ctx cod in
            cod_tm
        | name :: rest ->
            let ctx = Context.bind name dom_val ctx in
            let cod = bind_all ctx (n + 1) rest in
            TmPiHat (name, dom_tm_at n, cod)
      in
      (bind_all ctx 0 names, VTyU)
  | Arrow (dom, cod) ->
      let dom, _ = infer_tm genv ctx dom in
      let dom_val = do_el (eval_tm genv (Context.env ctx) dom) in
      let ctx = Context.bind None dom_val ctx in
      let cod_tm, _ = infer_tm genv ctx cod in
      (TmPiHat (None, dom, cod_tm), VTyU)
  | Sigma (binders, snd_ty) ->
      infer_tm genv ctx (Desugar.desugar_sigma binders snd_ty)
  | Prod (fst_ty, snd_ty) ->
      infer_tm genv ctx (Desugar.desugar_prod fst_ty snd_ty)
  | Pair (a, b) ->
      let a, a_ty = infer_tm genv ctx a in
      let b, b_ty = infer_tm genv ctx b in
      let a_code = reify_ty genv (Context.lvl ctx) a_ty in
      let b_code = reify_ty genv (Context.lvl ctx) b_ty in
      let prod_code = TmApp (TmApp (TmConst [ "Prod" ], a_code), b_code) in
      let pair_tm =
        TmApp
          ( TmApp (TmApp (TmApp (TmConst [ "Prod"; "mk" ], a_code), b_code), a),
            b )
      in
      let pair_ty = eval_ty genv (Context.env ctx) (TyEl prod_code) in
      (pair_tm, pair_ty)
  | NatLit n -> infer_tm genv ctx (Desugar.desugar_nat_lit n)
  | Add (a, b) -> infer_tm genv ctx (Desugar.desugar_add a b)
  | Sub (a, b) -> infer_tm genv ctx (Desugar.desugar_sub a b)
  | Eq (a, b) ->
      let a_tm, a_ty = infer_tm genv ctx a in
      let b_tm, _ = infer_tm genv ctx b in
      let a_ty_tm = reify_ty genv (Context.lvl ctx) a_ty in
      (TmApp (TmApp (TmApp (TmConst [ "Eq" ], a_ty_tm), a_tm), b_tm), VTyU)
  | Let (name, ty_opt, rhs, body) ->
      let rhs', rhs_ty =
        match ty_opt with
        | Some ty ->
            let ty' = check_ty genv ctx ty in
            let ty_val = eval_ty genv (Context.env ctx) ty' in
            (check_tm genv ctx rhs ty_val, ty_val)
        | None -> infer_tm genv ctx rhs
      in
      let rhs_val = eval_tm genv (Context.env ctx) rhs' in
      let ctx' = Context.bind_def (Some name) rhs_ty rhs_val ctx in
      let body', body_ty = infer_tm genv ctx' body in
      let body_ty_quoted = quote_ty genv (Context.lvl ctx') body_ty in
      let result_ty = eval_ty genv (Context.env ctx') body_ty_quoted in
      ( TmLet (name, quote_ty genv (Context.lvl ctx) rhs_ty, rhs', body'),
        result_ty )
  | Sorry ->
      let id = fresh_sorry_id () in
      let hole_ty = VTyEl (HConst [ Format.sprintf "?ty%d†" id ], []) in
      (TmSorry (id, quote_ty genv (Context.lvl ctx) hole_ty), hole_ty)

and check_tm (genv : Global.t) (ctx : Context.t) (raw : Raw_syntax.t)
    (expected : vl_ty) : tm =
  match (raw, expected) with
  | Lam (binders, body), _ ->
      let flatten_binders (binders : Raw_syntax.binder_group list) :
          (string option * Raw_syntax.t option) list =
        List.concat_map
          (function
            | Raw_syntax.Untyped name -> [ (Some name, None) ]
            | Raw_syntax.Typed (names, ty) ->
                List.map (fun name -> (name, Some ty)) names)
          binders
      in
      let rec go ctx expected = function
        | [] -> check_tm genv ctx body expected
        | (name, ty_opt) :: rest -> (
            match expected with
            | VTyPi (_, a_ty, ClosTy (env, b_ty)) ->
                (match ty_opt with
                | Some ann ->
                    let ann' = check_ty genv ctx ann in
                    let ann_val = eval_ty genv (Context.env ctx) ann' in
                    if not (conv_ty genv (Context.lvl ctx) ann_val a_ty) then
                      raise
                        (Elab_error
                           (Format.asprintf
                              "Lambda annotation mismatch: expected %a, got %a"
                              (Pretty.pp_ty_ctx (Context.names ctx))
                              (quote_ty genv (Context.lvl ctx) a_ty)
                              (Pretty.pp_ty_ctx (Context.names ctx))
                              (quote_ty genv (Context.lvl ctx) ann_val)))
                | None -> ());
                let ctx' = Context.bind name a_ty ctx in
                let var = VTmNeutral (HVar (Lvl (Context.lvl ctx)), []) in
                let b_ty_val = eval_ty genv (var :: env) b_ty in
                let body' = go ctx' b_ty_val rest in
                TmLam (name, quote_ty genv (Context.lvl ctx) a_ty, body')
            | _ -> raise (Elab_error "Expected function type for lambda"))
      in
      go ctx expected (flatten_binders binders)
  | Pair (a, b), VTyEl (HConst [ "Sigma" ], [ a_code_val; b_val ]) ->
      let fst_ty = do_el a_code_val in
      let a' = check_tm genv ctx a fst_ty in
      let a_val = eval_tm genv (Context.env ctx) a' in
      let b_code_val = do_app genv b_val a_val in
      let snd_ty = do_el b_code_val in
      let b' = check_tm genv ctx b snd_ty in
      let a_code_tm = quote_tm genv (Context.lvl ctx) a_code_val in
      let b_tm = quote_tm genv (Context.lvl ctx) b_val in
      TmApp
        ( TmApp (TmApp (TmApp (TmConst [ "Sigma"; "mk" ], a_code_tm), b_tm), a'),
          b' )
  | Pair (a, b), VTyEl (HConst [ "Prod" ], [ a_code_val; b_val ]) ->
      let fst_ty = do_el a_code_val in
      let snd_ty = do_el b_val in
      let a' = check_tm genv ctx a fst_ty in
      let b' = check_tm genv ctx b snd_ty in
      let a_code_tm = quote_tm genv (Context.lvl ctx) a_code_val in
      let b_code_tm = quote_tm genv (Context.lvl ctx) b_val in
      TmApp
        ( TmApp
            (TmApp (TmApp (TmConst [ "Prod"; "mk" ], a_code_tm), b_code_tm), a'),
          b' )
  | Pair (_, _), VTyEl (HConst [ _ ], [ _; _ ]) ->
      raise (Elab_error "Expected sigma/product type in pair")
  | Let (name, ty_opt, rhs, body), expected ->
      let rhs', rhs_ty =
        match ty_opt with
        | Some ty ->
            let ty' = check_ty genv ctx ty in
            let ty_val = eval_ty genv (Context.env ctx) ty' in
            (check_tm genv ctx rhs ty_val, ty_val)
        | None -> infer_tm genv ctx rhs
      in
      let rhs_val = eval_tm genv (Context.env ctx) rhs' in
      let ctx' = Context.bind_def (Some name) rhs_ty rhs_val ctx in
      let body' = check_tm genv ctx' body expected in
      TmLet (name, quote_ty genv (Context.lvl ctx) rhs_ty, rhs', body')
  | Sorry, expected ->
      let id = fresh_sorry_id () in
      TmSorry (id, quote_ty genv (Context.lvl ctx) expected)
  | _ ->
      let tm, inferred = infer_tm genv ctx raw in
      (if not (conv_ty genv (Context.lvl ctx) inferred expected) then
         let names = Context.names ctx in
         raise
           (Elab_error
              (Format.asprintf "Type mismatch: expected %a, got %a"
                 (Pretty.pp_ty_ctx names)
                 (quote_ty genv (Context.lvl ctx) expected)
                 (Pretty.pp_ty_ctx names)
                 (quote_ty genv (Context.lvl ctx) inferred))));
      tm

(* ========== Positivity Checking ========== *)

let rec has_ind_occ_ty (ind : Name.t) : ty -> bool = function
  | TyU -> false
  | TyPi (_, a, b) -> has_ind_occ_ty ind a || has_ind_occ_ty ind b
  | TyEl t -> has_ind_occ_tm ind t

and has_ind_occ_tm (ind : Name.t) : tm -> bool = function
  | TmVar _ -> false
  | TmConst name -> name = ind
  | TmLam (_, a, body) -> has_ind_occ_ty ind a || has_ind_occ_tm ind body
  | TmApp (f, a) -> has_ind_occ_tm ind f || has_ind_occ_tm ind a
  | TmPiHat (_, a, b) -> has_ind_occ_tm ind a || has_ind_occ_tm ind b
  | TmSorry (_, ty) -> has_ind_occ_ty ind ty
  | TmLet (_, ty, t, body) ->
      has_ind_occ_ty ind ty || has_ind_occ_tm ind t || has_ind_occ_tm ind body

let rec is_valid_ind_app (ind : Name.t) : tm -> bool = function
  | TmConst name -> name = ind
  | TmApp (f, _) -> is_valid_ind_app ind f
  | _ -> false

let rec get_app_head : tm -> Name.t option = function
  | TmConst name -> Some name
  | TmApp (f, _) -> get_app_head f
  | _ -> None

let rec has_var_ty (var_idx : int) : ty -> bool = function
  | TyU -> false
  | TyPi (_, a, b) -> has_var_ty var_idx a || has_var_ty (var_idx + 1) b
  | TyEl t -> has_var_tm var_idx t

and has_var_tm (var_idx : int) : tm -> bool = function
  | TmVar (Idx i) -> i = var_idx
  | TmConst _ -> false
  | TmLam (_, a, body) -> has_var_ty var_idx a || has_var_tm (var_idx + 1) body
  | TmApp (f, a) -> has_var_tm var_idx f || has_var_tm var_idx a
  | TmPiHat (_, a, b) -> has_var_tm var_idx a || has_var_tm (var_idx + 1) b
  | TmSorry (_, ty) -> has_var_ty var_idx ty
  | TmLet (_, ty, t, body) ->
      has_var_ty var_idx ty || has_var_tm var_idx t
      || has_var_tm (var_idx + 1) body

(* Check if var appears negatively (on the left of an arrow) *)
let rec var_occurs_negatively_ty (var_idx : int) : ty -> bool = function
  | TyU -> false
  | TyPi (_, a, b) ->
      has_var_ty var_idx a || var_occurs_negatively_ty (var_idx + 1) b
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
  | TmSorry (_, ty) -> var_occurs_negatively_ty var_idx ty
  | TmLet (_, ty, t, body) ->
      var_occurs_negatively_ty var_idx ty
      || var_occurs_negatively_tm var_idx t
      || var_occurs_negatively_tm (var_idx + 1) body

(* Check if inductive F is strictly positive in its first parameter *)
let check_inductive_param_positive (genv : Global.t) (f_name : Name.t) : bool =
  match Global.find_inductive f_name genv with
  | None -> false
  | Some info ->
      let rec count_params = function
        | TyPi (_, _, b) -> 1 + count_params b
        | _ -> 0
      in
      let n_params = count_params info.ty in
      if n_params = 0 then
        true
      else
        let check_ctor_positive (_ctor_name, ctor_ty) =
          let rec skip_and_check skip depth = function
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

let rec check_positivity_ty (genv : Global.t) (ind : Name.t) : ty -> unit =
  function
  | TyU -> ()
  | TyPi (_, a, b) ->
      if has_ind_occ_ty ind a then
        raise
          (Elab_error
             (Format.sprintf "%s has a non-positive occurrence (in domain)"
                (Name.to_string ind)));
      check_positivity_ty genv ind b
  | TyEl t -> check_positivity_tm genv ind t

and check_positivity_tm (genv : Global.t) (ind : Name.t) (tm : tm) : unit =
  if has_ind_occ_tm ind tm && not (is_valid_ind_app ind tm) then
    match tm with
    | TmVar _ -> ()
    | TmConst _ -> ()
    | TmPiHat (_, a, b) ->
        if has_ind_occ_tm ind a then
          raise
            (Elab_error
               (Format.sprintf "%s has a non-positive occurrence (in domain)"
                  (Name.to_string ind)));
        check_positivity_tm genv ind b
    | TmApp (_, _) -> (
        match get_app_head tm with
        | Some f_name when Option.is_some (Global.find_inductive f_name genv) ->
            if not (check_inductive_param_positive genv f_name) then
              raise
                (Elab_error
                   (Format.sprintf
                      "%s has a non-positive occurrence (nested in %s)"
                      (Name.to_string ind) (Name.to_string f_name)))
        | _ ->
            raise
              (Elab_error
                 (Format.sprintf "%s has a non-valid occurrence (nested)"
                    (Name.to_string ind))))
    | TmLam (_, a, body) ->
        check_positivity_ty genv ind a;
        check_positivity_tm genv ind body
    | _ ->
        raise
          (Elab_error
             (Format.sprintf "%s has a non-valid occurrence"
                (Name.to_string ind)))

let rec check_strict_positivity (genv : Global.t) (ind : Name.t) : ty -> unit =
  function
  | TyPi (_, a, b) ->
      check_positivity_ty genv ind a;
      check_strict_positivity genv ind b
  | _ -> ()

let rec check_returns_inductive (ind : Name.t) : ty -> bool = function
  | TyEl (TmConst name) -> name = ind
  | TyEl (TmApp (f, _)) -> check_returns_inductive_tm ind f
  | TyPi (_, _, b) -> check_returns_inductive ind b
  | _ -> false

and check_returns_inductive_tm (ind : Name.t) : tm -> bool = function
  | TmConst name -> name = ind
  | TmApp (f, _) -> check_returns_inductive_tm ind f
  | _ -> false

let check_return_params (ctor_name : Name.t) (ind : Name.t) (num_params : int)
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
      if head = TmConst ind && List.length args < num_params then
        raise
          (Elab_error
             (Format.sprintf "%s: return type must apply %s to all parameters"
                (Name.to_string ctor_name) (Name.to_string ind)))

(* ========== Inductive Types ========== *)

let elab_ctor (genv : Global.t) (ind : Name.t) (param_ctx : Context.t)
    (param_tys : (string option * ty) list) (num_params : int)
    (ctor : Raw_syntax.constructor) : Name.t * ty * vl_ty =
  let full_name = Name.child ind ctor.name in
  let flatten_params (params : Raw_syntax.typed_binder_group list) :
      (string option * Raw_syntax.t option) list =
    List.concat_map
      (fun (names, ty) -> List.map (fun name -> (name, Some ty)) names)
      params
  in
  let rec build_ctor_body ctx depth = function
    | [] -> (
        match ctor.ty with
        | None ->
            let base = TmConst ind in
            let applied =
              List.fold_left
                (fun acc i ->
                  TmApp (acc, TmVar (Idx (depth + num_params - 1 - i))))
                base
                (List.init num_params Fun.id)
            in
            TyEl applied
        | Some ret_raw ->
            let ret_ty = check_ty genv ctx ret_raw in
            if not (check_returns_inductive ind ret_ty) then
              raise
                (Elab_error
                   (Format.sprintf "%s must return %s"
                      (Name.to_string full_name) (Name.to_string ind)));
            check_return_params full_name ind num_params ret_ty;
            ret_ty)
    | (name, ty_opt) :: rest ->
        let param_ty =
          match ty_opt with
          | Some ty_raw -> check_ty genv ctx ty_raw
          | None ->
              raise
                (Elab_error
                   (Format.sprintf "%s: parameter needs type"
                      (Name.to_string full_name)))
        in
        let param_ty_val = eval_ty genv (Context.env ctx) param_ty in
        let ctx' = Context.bind name param_ty_val ctx in
        let body_ty = build_ctor_body ctx' (depth + 1) rest in
        TyPi (name, param_ty, body_ty)
  in
  let ctor_body = build_ctor_body param_ctx 0 (flatten_params ctor.params) in
  let ctor_ty =
    List.fold_right
      (fun (name, ty) body -> TyPi (name, ty, body))
      param_tys ctor_body
  in
  check_strict_positivity genv ind ctor_ty;
  let ctor_ty_val = eval_ty genv [] ctor_ty in
  (full_name, ctor_ty, ctor_ty_val)

(* ========== Recursor Generation ========== *)

let rec is_recursive_arg_ty (ind : Name.t) : ty -> bool = function
  | TyEl (TmConst name) -> name = ind
  | TyEl (TmApp (f, _)) -> is_recursive_arg_tm ind f
  | TyPi (_, _, b) -> is_recursive_arg_ty ind b
  | _ -> false

and is_recursive_arg_tm (ind : Name.t) : tm -> bool = function
  | TmConst name -> name = ind
  | TmApp (f, _) -> is_recursive_arg_tm ind f
  | _ -> false

let extract_app_args : tm -> tm list =
  let rec go acc = function
    | TmApp (f, a) -> go (a :: acc) f
    | _ -> List.rev acc
  in
  go []

let rec extract_indices : ty -> (string option * ty) list = function
  | TyPi (name, a, b) -> (name, a) :: extract_indices b
  | TyU -> []
  | _ -> []

let rec extract_return_indices_from_ctor (ind : Name.t) (num_params : int) :
    ty -> tm list = function
  | TyPi (_, _, b) -> extract_return_indices_from_ctor ind num_params b
  | TyEl tm -> extract_args_after_params ind num_params tm
  | _ -> []

and extract_args_after_params (ind : Name.t) (num_params : int) (tm : tm) :
    tm list =
  let rec collect_all_args acc = function
    | TmConst name when name = ind -> acc
    | TmApp (f, a) -> collect_all_args (a :: acc) f
    | _ -> []
  in
  let all_args = collect_all_args [] tm in
  if List.length all_args >= num_params then
    List.drop num_params all_args
  else
    []

let extract_nested_rec_info (ind : Name.t) (num_params : int) (ty : ty) :
    (string option * ty) list * tm list =
  let rec go acc = function
    | TyPi (name, arg_ty, body) -> go ((name, arg_ty) :: acc) body
    | TyEl tm ->
        let indices = extract_args_after_params ind num_params tm in
        (List.rev acc, indices)
    | _ -> (List.rev acc, [])
  in
  go [] ty

(* Generate recursor type for an inductive *)
let gen_recursor_ty (genv : Global.t) (ind : Name.t) (num_params : int)
    (param_tys : (string option * ty) list)
    (index_tys : (string option * ty) list) (ctor_tys : (Name.t * ty) list) :
    vl_ty =
  let app arg fn = do_app genv fn arg in
  let apps args fn = List.fold_left (do_app genv) fn args in

  let index_tys =
    List.mapi
      (fun i (name_opt, ty) ->
        match name_opt with
        | Some _ -> (name_opt, ty)
        | None -> (Some (Format.sprintf "a%d†" i), ty))
      index_tys
  in

  let mk_pi (lvl : int) (env : env) (name : string option) (dom : vl_ty)
      (body : vl_tm -> vl_ty) : vl_ty =
    let var = VTmNeutral (HVar (Lvl lvl), []) in
    let body_val = body var in
    let body_ty = quote_ty genv (lvl + 1) body_val in
    VTyPi (name, dom, ClosTy (env, body_ty))
  in

  let ind_code : vl_tm = VTmNeutral (HConst ind, []) in
  let ctor_code (ctor : Name.t) : vl_tm = VTmNeutral (HConst ctor, []) in

  let mk_ind_ty (params_order : vl_tm list) (indices_order : vl_tm list) : vl_ty
      =
    do_el (ind_code |> apps params_order |> apps indices_order)
  in

  let build_motive_ty (params_rev : env) (params_order : vl_tm list) : vl_ty =
    let rec go_indices (lvl : int) (env : env) (indices_rev : env)
        (indices_order : vl_tm list) = function
      | [] ->
          let x_ty = mk_ind_ty params_order indices_order in
          mk_pi lvl env None x_ty (fun _ -> VTyU)
      | (name, idx_ty) :: rest ->
          let dom = eval_ty genv (indices_rev @ params_rev) idx_ty in
          mk_pi lvl env name dom (fun idx ->
              go_indices (lvl + 1) (idx :: env) (idx :: indices_rev)
                (indices_order @ [ idx ]) rest)
    in
    go_indices (List.length params_rev) params_rev [] [] index_tys
  in

  let build_method_ty (outer_lvl : int) (outer_env : env) (params_rev : env)
      (params_order : vl_tm list) (motive : vl_tm) (ctor_name : Name.t)
      (ctor_ty : ty) : vl_ty =
    let rec strip_params n ty =
      if n = 0 then
        ty
      else
        match ty with
        | TyPi (_, _, b) -> strip_params (n - 1) b
        | ty -> ty
    in
    let fields_ty = strip_params num_params ctor_ty in

    let rec collect_fields acc = function
      | TyPi (name, arg_ty, rest) ->
          collect_fields
            ((name, arg_ty, is_recursive_arg_ty ind arg_ty) :: acc)
            rest
      | _ -> List.rev acc
    in
    let fields = collect_fields [] fields_ty in

    let return_indices =
      extract_return_indices_from_ctor ind num_params ctor_ty
    in

    let rec bind_fields (lvl : int) (env : env) (fields_rev : env)
        (fields_order : vl_tm list) : (string option * ty * bool) list -> vl_ty
        = function
      | [] ->
          let env_for_return = fields_rev @ params_rev in
          let idx_vals =
            List.map (eval_tm genv env_for_return) return_indices
          in
          let motive_app = motive |> apps idx_vals in
          let ctor_app =
            ctor_code ctor_name |> apps params_order |> apps fields_order
          in
          let result_ty = do_el (motive_app |> app ctor_app) in
          let rec_field_infos =
            let rec go i acc = function
              | [] -> List.rev acc
              | (name, field_ty, is_rec) :: rest ->
                  if is_rec then
                    go (i + 1) ((i, name, field_ty) :: acc) rest
                  else
                    go (i + 1) acc rest
            in
            go 0 [] fields
          in

          let ih_infos =
            List.map
              (fun (i, name, field_ty) ->
                let field_var = List.nth fields_order i in
                let prefix_rev = List.rev (List.take i fields_order) in
                let nested_binders, rec_indices =
                  extract_nested_rec_info ind num_params field_ty
                in

                let rec mk_ih_ty (lvl : int) (env : env) (nested_rev : env)
                    (nested_order : vl_tm list) (binder_idx : int) :
                    (string option * ty) list -> vl_ty = function
                  | [] ->
                      let env_for_indices =
                        nested_rev @ prefix_rev @ params_rev
                      in
                      let idx_vals =
                        List.map (eval_tm genv env_for_indices) rec_indices
                      in
                      do_el
                        (motive |> apps idx_vals
                        |> app (field_var |> apps nested_order))
                  | (n, ty) :: rest ->
                      let dom =
                        eval_ty genv (nested_rev @ prefix_rev @ params_rev) ty
                      in
                      let binder_name =
                        match n with
                        | Some name -> Some name
                        | None -> Some (Format.sprintf "a%d†" binder_idx)
                      in
                      mk_pi lvl env binder_name dom (fun v ->
                          mk_ih_ty (lvl + 1) (v :: env) (v :: nested_rev)
                            (nested_order @ [ v ]) (binder_idx + 1) rest)
                in

                let ih_ty = mk_ih_ty lvl env [] [] 0 nested_binders in
                let ih_name =
                  Some (Format.sprintf "%s_ih" (Option.value name ~default:"x"))
                in
                (ih_name, ih_ty))
              rec_field_infos
          in

          let rec bind_ihs (lvl : int) (env : env) :
              (string option * vl_ty) list -> vl_ty = function
            | [] -> result_ty
            | (ih_name, ih_ty) :: rest ->
                mk_pi lvl env ih_name ih_ty (fun ih ->
                    bind_ihs (lvl + 1) (ih :: env) rest)
          in
          bind_ihs lvl env ih_infos
      | (name, field_ty, _is_rec) :: rest ->
          let dom = eval_ty genv (fields_rev @ params_rev) field_ty in
          mk_pi lvl env name dom (fun v ->
              bind_fields (lvl + 1) (v :: env) (v :: fields_rev)
                (fields_order @ [ v ]) rest)
    in
    bind_fields outer_lvl outer_env [] [] fields
  in

  let rec build_params (lvl : int) (env : env) (params_rev : env)
      (params_order : vl_tm list) : (string option * ty) list -> vl_ty =
    function
    | [] ->
        let motive_dom = build_motive_ty params_rev params_order in
        mk_pi lvl env (Some "motive") motive_dom (fun motive ->
            let rec build_methods (lvl : int) (env : env) :
                (Name.t * ty) list -> vl_ty = function
              | [] -> build_indices lvl env motive [] []
              | (ctor_name, ctor_ty) :: rest ->
                  let method_ty =
                    build_method_ty lvl env params_rev params_order motive
                      ctor_name ctor_ty
                  in
                  mk_pi lvl env None method_ty (fun _m ->
                      build_methods (lvl + 1) (_m :: env) rest)
            and build_indices (lvl : int) (env : env) (motive : vl_tm)
                (indices_rev : env) (indices_order : vl_tm list) : vl_ty =
              match List.drop (List.length indices_order) index_tys with
              | [] ->
                  let x_ty = mk_ind_ty params_order indices_order in
                  mk_pi lvl env None x_ty (fun t ->
                      let motive_app = motive |> apps indices_order in
                      do_el (do_app genv motive_app t))
              | (name, idx_ty) :: _rest ->
                  let dom = eval_ty genv (indices_rev @ params_rev) idx_ty in
                  mk_pi lvl env name dom (fun idx ->
                      build_indices (lvl + 1) (idx :: env) motive
                        (idx :: indices_rev) (indices_order @ [ idx ]))
            in
            build_methods (lvl + 1) (motive :: env) ctor_tys)
    | (name, ty) :: rest ->
        let dom = eval_ty genv params_rev ty in
        mk_pi lvl env name dom (fun v ->
            build_params (lvl + 1) (v :: env) (v :: params_rev)
              (params_order @ [ v ]) rest)
  in

  build_params 0 [] [] [] param_tys

let elab_inductive (genv : Global.t) (ind : Raw_syntax.inductive_info) :
    Global.t * (Name.t * tm * ty) list =
  let ind_name = Name.parse ind.name in
  let rec elab_params ctx acc_tys = function
    | [] -> (ctx, List.rev acc_tys)
    | (names, ty_raw) :: rest ->
        let param_ty = check_ty genv ctx ty_raw in
        let param_ty_val = eval_ty genv (Context.env ctx) param_ty in
        let ctx', tys =
          List.fold_left
            (fun (c, ts) name ->
              (Context.bind name param_ty_val c, (name, param_ty) :: ts))
            (ctx, acc_tys) names
        in
        elab_params ctx' tys rest
  in
  let param_ctx, param_tys = elab_params Context.empty [] ind.params in
  let num_params = List.length param_tys in
  let result_ty =
    match ind.ty with
    | None -> TyU
    | Some ty_raw -> check_ty genv param_ctx ty_raw
  in
  let ty =
    List.fold_right
      (fun (name, ty) body -> TyPi (name, ty, body))
      param_tys result_ty
  in
  let ind_ty_val = eval_ty genv [] ty in
  let genv =
    Global.NameMap.add ind_name (Global.Opaque { ty = ind_ty_val }) genv
  in
  let ctor_results =
    List.map (elab_ctor genv ind_name param_ctx param_tys num_params) ind.ctors
  in
  let genv =
    List.fold_left
      (fun g (ctor_idx, (name, _ty, ty_val)) ->
        Global.NameMap.add name
          (Global.Constructor { ty = ty_val; ind_name; ctor_idx })
          g)
      genv
      (List.mapi (fun i x -> (i, x)) ctor_results)
  in
  let ctor_name_tys = List.map (fun (name, ty, _) -> (name, ty)) ctor_results in
  let genv =
    Global.NameMap.add ind_name
      (Global.Inductive { ty; ctors = ctor_name_tys })
      genv
  in
  let rec_name = Name.child ind_name "rec" in
  let index_tys = extract_indices result_ty in
  let num_indices = List.length index_tys in
  let rec_ty_val =
    gen_recursor_ty genv ind_name num_params param_tys index_tys ctor_name_tys
  in
  let rec_rules =
    List.map
      (fun (ctor_name, ctor_ty) ->
        let fields_ty =
          let rec strip n t =
            if n = 0 then
              t
            else
              match t with
              | TyPi (_, _, b) -> strip (n - 1) b
              | _ -> t
          in
          strip num_params ctor_ty
        in
        let rec collect_fields idx = function
          | TyPi (_, arg_ty, rest) ->
              let is_rec = is_recursive_arg_ty ind_name arg_ty in
              (idx, is_rec) :: collect_fields (idx + 1) rest
          | _ -> []
        in
        let all_fields = collect_fields 0 fields_ty in
        let nfields = List.length all_fields in
        let rec_args =
          List.filter_map
            (fun (idx, is_rec) ->
              if is_rec then
                Some idx
              else
                None)
            all_fields
        in
        let rec_indices =
          List.map
            (fun rec_idx ->
              let rec get_field_ty n = function
                | TyPi (_, arg_ty, rest) ->
                    if n = 0 then
                      arg_ty
                    else
                      get_field_ty (n - 1) rest
                | _ -> TyU
              in
              let field_ty = get_field_ty rec_idx fields_ty in
              let rec extract_indices_from_ty = function
                | TyEl tm -> extract_app_args tm
                | TyPi (_, _, b) -> extract_indices_from_ty b
                | _ -> []
              in
              let args = extract_indices_from_ty field_ty in
              let index_args =
                if List.length args > num_params then
                  List.drop num_params args
                else
                  []
              in
              List.filter_map
                (function
                  | TmVar (Idx i) ->
                      let field_num = rec_idx - 1 - i in
                      if field_num >= 0 && field_num < nfields then
                        Some field_num
                      else
                        None
                  | _ -> None)
                index_args)
            rec_args
        in
        Global.
          {
            rule_ctor_name = ctor_name;
            rule_nfields = nfields;
            rule_rec_args = rec_args;
            rule_rec_indices = rec_indices;
          })
      ctor_name_tys
  in
  let rec_info : Global.recursor_info =
    {
      ty = rec_ty_val;
      rec_ind_name = ind_name;
      rec_num_params = num_params;
      rec_num_indices = num_indices;
      rec_num_motives = 1;
      rec_num_methods = List.length ctor_name_tys;
      rec_rules;
    }
  in
  let genv = Global.NameMap.add rec_name (Global.Recursor rec_info) genv in
  let rec_ty = quote_ty genv 0 rec_ty_val in
  let results = (ind_name, ty) :: (rec_name, rec_ty) :: ctor_name_tys in
  let results' =
    List.fold_left (fun acc (n, ty) -> (n, TmConst n, ty) :: acc) [] results
  in
  (genv, results')

let elab_structure (genv : Global.t) (info : Raw_syntax.structure_info) :
    Global.t * (Name.t * tm * ty) list =
  let ind_name = Name.parse info.name in
  let () =
    match info.ty with
    | None -> ()
    | Some Raw_syntax.U -> ()
    | Some _ -> raise (Elab_error "Structure result type must be Type")
  in
  let mk_field_ty (field : Raw_syntax.field) : Raw_syntax.t =
    List.fold_right
      (fun bg body -> Raw_syntax.Pi (bg, body))
      field.binders field.ty
  in
  let ctor_binders : Raw_syntax.typed_binder_group list =
    List.map
      (fun (field : Raw_syntax.field) ->
        ([ Some field.name ], mk_field_ty field))
      info.fields
  in
  let ctors : Raw_syntax.constructor list =
    [ { name = "mk"; params = ctor_binders; ty = None } ]
  in
  let genv, results =
    elab_inductive genv
      { name = info.name; params = info.params; ty = info.ty; ctors }
  in
  let struct_info : Global.structure_info =
    {
      struct_ind_name = ind_name;
      struct_ctor_name = Name.child ind_name "mk";
      struct_num_params =
        List.fold_left
          (fun n ((ns, _) : Raw_syntax.typed_binder_group) ->
            n + List.length ns)
          0 info.params;
      struct_num_fields = List.length info.fields;
      struct_field_names =
        List.map (fun (field : Raw_syntax.field) -> field.name) info.fields;
    }
  in
  let genv =
    match Global.find_opt ind_name genv with
    | Some (Global.Inductive ind) ->
        Global.NameMap.add ind_name
          (Global.Structure { ind; info = struct_info })
          genv
    | _ -> genv
  in
  let param_names =
    List.concat_map
      (fun ((ns, _) : Raw_syntax.typed_binder_group) -> ns)
      info.params
  in
  let make_proj_app fname : Raw_syntax.t =
    let base =
      List.fold_left
        (fun acc -> function
          | Some n -> Raw_syntax.App (acc, Raw_syntax.Ident n)
          | None -> acc)
        (Raw_syntax.Ident (info.name ^ "." ^ fname))
        param_names
    in
    App (base, Ident "s")
    (* TODO: use a fresh name *)
  in
  let rec subst_fields ef : Raw_syntax.t -> Raw_syntax.t = function
    | Ident x -> (
        match List.assoc_opt x ef with
        | Some proj -> proj
        | None -> Ident x)
    | App (f, a) -> App (subst_fields ef f, subst_fields ef a)
    | Lam (bs, body) ->
        let bound =
          List.concat_map
            (function
              | Raw_syntax.Untyped name -> [ name ]
              | Raw_syntax.Typed (names, _) -> List.filter_map Fun.id names)
            bs
        in
        let earlier_fields' =
          List.filter (fun (n, _) -> not (List.mem n bound)) ef
        in
        let bs' =
          List.map
            (function
              | Raw_syntax.Untyped name -> Raw_syntax.Untyped name
              | Raw_syntax.Typed (names, ty) ->
                  Raw_syntax.Typed (names, subst_fields ef ty))
            bs
        in
        Lam (bs', subst_fields earlier_fields' body)
    | Pi ((ns, ty), body) ->
        let bound = List.filter_map Fun.id ns in
        let earlier_fields' =
          List.filter (fun (n, _) -> not (List.mem n bound)) ef
        in
        Pi ((ns, subst_fields ef ty), subst_fields earlier_fields' body)
    | Arrow (a, b) -> Arrow (subst_fields ef a, subst_fields ef b)
    | Raw_syntax.Prod (a, b) -> Prod (subst_fields ef a, subst_fields ef b)
    | Pair (a, b) -> Raw_syntax.Pair (subst_fields ef a, subst_fields ef b)
    | Eq (a, b) -> Eq (subst_fields ef a, subst_fields ef b)
    | Add (a, b) -> Add (subst_fields ef a, subst_fields ef b)
    | Sub (a, b) -> Sub (subst_fields ef a, subst_fields ef b)
    | Sigma ((ns, a), b) ->
        let bound = List.filter_map Fun.id ns in
        let earlier_fields' =
          List.filter (fun (n, _) -> not (List.mem n bound)) ef
        in
        Sigma ((ns, subst_fields ef a), subst_fields earlier_fields' b)
    | Ann (t, ty) -> Ann (subst_fields ef t, subst_fields ef ty)
    | Let (n, ty_opt, t, b) ->
        let earlier_fields' = List.filter (fun (x, _) -> x <> n) ef in
        Let
          ( n,
            Option.map (subst_fields ef) ty_opt,
            subst_fields ef t,
            subst_fields earlier_fields' b )
    | tm -> tm
  in
  let rec_app =
    List.fold_left
      (fun acc -> function
        | Some n -> Raw_syntax.App (acc, Raw_syntax.Ident n)
        | None -> acc)
      (Raw_syntax.Ident (info.name ^ ".rec"))
      param_names
  in
  let field_binders : Raw_syntax.binder_group list =
    List.map
      (fun (field : Raw_syntax.field) -> Raw_syntax.Untyped field.name)
      info.fields
  in
  let param_binders : Raw_syntax.binder_group list =
    List.map
      (fun ((names, ty) : Raw_syntax.typed_binder_group) ->
        Raw_syntax.Typed (names, ty))
      info.params
  in
  let genv, results =
    List.fold_left
      (fun (genv, acc) (field : Raw_syntax.field) ->
        let proj_name = Name.child (Name.parse info.name) field.name in
        let field_ty = mk_field_ty field in
        let subst_fty =
          subst_fields
            (List.filter_map
               (fun other_fname ->
                 if String.equal other_fname field.name then
                   None
                 else
                   Some (other_fname, make_proj_app other_fname))
               (List.map
                  (fun (field : Raw_syntax.field) -> field.name)
                  info.fields))
            field_ty
        in
        let body : Raw_syntax.t =
          App
            ( App (rec_app, Lam ([ Raw_syntax.Untyped "s" ], subst_fty)),
              Lam (field_binders, Ident field.name) )
        in
        let full_def =
          match param_binders with
          | [] -> body
          | _ -> Lam (param_binders, body)
        in
        let term, ty_val = infer_tm genv Context.empty full_def in
        let term_val = eval_tm genv [] term in
        let genv =
          Global.NameMap.add proj_name
            (Global.Def { ty = ty_val; tm = term_val })
            genv
        in
        let ty_out = quote_ty genv 0 ty_val in
        (genv, (proj_name, term, ty_out) :: acc))
      (genv, results) info.fields
  in
  (genv, results)

(* ========== Program Elaboration ========== *)

exception Circular_import of Name.t
exception Import_not_found of Name.t

module ModuleNameSet = Set.Make (Name)

let elab_program_with_imports ~(root : string) ~(read_file : string -> string)
    ~(parse : string -> Raw_syntax.program) (prog : Raw_syntax.program) :
    (Name.t * tm * ty) list =
  let rec process_import genv imported importing m =
    if List.mem m importing then raise (Circular_import m);
    if ModuleNameSet.mem m imported then
      (genv, imported)
    else
      let path = Filename.concat root (String.concat "/" m ^ ".qdt") in
      let content =
        try read_file path with
        | _ -> raise (Import_not_found m)
      in
      let imported_prog = parse content in
      let genv, imported, _ =
        go genv imported (m :: importing) [] imported_prog
      in
      (genv, ModuleNameSet.add m imported)
  and go genv imported importing acc = function
    | [] -> (genv, imported, List.rev acc)
    | Import { module_name } :: rest ->
        let m = Name.parse module_name in
        let genv, imported = process_import genv imported importing m in
        go genv imported importing acc rest
    | Def { name; body } :: rest ->
        let full_name = Name.parse name in
        let term, ty_val = infer_tm genv Context.empty body in
        let term_val = eval_tm genv [] term in
        let genv =
          Global.NameMap.add full_name
            (Global.Def { ty = ty_val; tm = term_val })
            genv
        in
        let ty_out = quote_ty genv 0 ty_val in
        go genv imported importing ((full_name, term, ty_out) :: acc) rest
    | Example { body } :: rest ->
        let _ = infer_tm genv Context.empty body in
        go genv imported importing acc rest
    | Inductive info :: rest ->
        let genv, results = elab_inductive genv info in
        go genv imported importing (results @ acc) rest
    | Structure info :: rest ->
        let genv, results = elab_structure genv info in
        go genv imported importing (results @ acc) rest
  in
  let genv, _, result = go Global.empty ModuleNameSet.empty [] [] prog in
  Format.printf "Elaborated %d definitions\n" (Global.NameMap.cardinal genv);
  result

let elab_program : Raw_syntax.program -> (Name.t * tm * ty) list =
  elab_program_with_imports ~root:"."
    ~read_file:(fun _ -> "")
    ~parse:(fun _ -> [])
