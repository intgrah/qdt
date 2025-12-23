open Syntax

exception Elab_error of string

module NameMap = Map.Make (Name)
module ModuleSet = Set.Make (Module_name)

let fresh_sorry_id =
  let counter = ref 0 in
  fun () ->
    let id = !counter in
    incr counter;
    id

(* ========== Global Environment ========== *)

module GlobalEnv = struct
  type inductive_info = {
    ty : ty;
    ctors : (Name.t * ty) list;
  }

  type rec_rule = {
    rule_ctor_name : Name.t;
    rule_nfields : int;
    rule_rec_args : int list;
    rule_rec_indices : int list list;
  }

  type recursor_info = {
    ty : vl_ty;
    rec_ind_name : Name.t;
    rec_num_params : int;
    rec_num_indices : int;
    rec_num_motives : int;
    rec_num_methods : int;
    rec_rules : rec_rule list;
  }

  type structure_info = {
    struct_ind_name : Name.t;
    struct_ctor_name : Name.t;
    struct_num_params : int;
    struct_num_fields : int;
    struct_field_names : string list;
  }

  type constructor_info = {
    ty : vl_ty;
    ind_name : Name.t;
    ctor_idx : int;
  }

  type entry =
    | Def of {
        ty : vl_ty;
        tm : vl_tm;
      }
    | Opaque of { ty : vl_ty } (* Type formers, e.g. Eq, Nat *)
    | Inductive of inductive_info
    | Structure of {
        ind : inductive_info;
        info : structure_info;
      }
    | Recursor of recursor_info
    | Constructor of constructor_info

  type t = entry NameMap.t

  let empty : t = NameMap.empty
  let find_opt = NameMap.find_opt

  let find_tm name env =
    match find_opt name env with
    | Some (Def { tm; _ }) -> Some tm
    | _ -> None

  let find_recursor name env =
    match find_opt name env with
    | Some (Recursor info) -> Some info
    | _ -> None

  let find_constructor name env =
    match find_opt name env with
    | Some (Constructor info) -> Some info
    | _ -> None

  let find_inductive name env =
    match find_opt name env with
    | Some (Inductive info) -> Some info
    | Some (Structure { ind; _ }) -> Some ind
    | _ -> None

  let find_structure name env =
    match find_opt name env with
    | Some (Structure { info; _ }) -> Some info
    | _ -> None
end

(* ========== Evaluation ========== *)

let rec eval_ty (genv : GlobalEnv.t) (env : env) : ty -> vl_ty = function
  | TyU -> VTyU
  | TyPi (x, a, b) -> VTyPi (x, eval_ty genv env a, ClosTy (env, b))
  | TyEl t -> do_el (eval_tm genv env t)

and do_el : vl_tm -> vl_ty = function
  | VTmPiHat (x, a, ClosTm (env', b)) ->
      VTyPi (x, do_el a, ClosTy (env', TyEl b))
  | VTmNeutral n -> VTyEl n
  | _ -> raise (Elab_error "do_el: expected type code or neutral")

and eval_tm (genv : GlobalEnv.t) (env : env) : tm -> vl_tm = function
  | TmVar (Idx l) -> List.nth env l
  | TmConst name -> (
      match GlobalEnv.find_tm name genv with
      | Some v -> v
      | None -> VTmNeutral (HConst name, []))
  | TmLam (x, a, body) -> VTmLam (x, eval_ty genv env a, ClosTm (env, body))
  | TmApp (f, a) -> do_app genv (eval_tm genv env f) (eval_tm genv env a)
  | TmPiHat (x, a, b) -> VTmPiHat (x, eval_tm genv env a, ClosTm (env, b))
  | TmSorry (id, ty) -> VTmNeutral (HSorry (id, eval_ty genv env ty), [])
  | TmLet (_, _, t, body) -> eval_tm genv (eval_tm genv env t :: env) body

and do_app (genv : GlobalEnv.t) (f : vl_tm) (a : vl_tm) : vl_tm =
  match f with
  | VTmLam (_, _, ClosTm (env, body)) -> eval_tm genv (a :: env) body
  | VTmNeutral (h, sp) -> (
      let ne : neutral = (h, sp @ [ a ]) in
      match try_iota_reduce genv ne with
      | Some v -> v
      | None -> VTmNeutral ne)
  | _ -> raise (Elab_error "do_app: expected lambda or neutral")

and try_iota_reduce (genv : GlobalEnv.t) : neutral -> vl_tm option = function
  | HConst rec_name, sp -> (
      match GlobalEnv.find_recursor rec_name genv with
      | None -> None
      | Some info -> (
          let major_idx =
            info.rec_num_params + info.rec_num_motives + info.rec_num_methods
            + info.rec_num_indices
          in
          if List.length sp <= major_idx then
            None
          else
            let major = List.nth sp major_idx in
            match major with
            | VTmNeutral (HConst ctor_name, ctor_sp) -> (
                match
                  List.find_opt
                    (fun r -> r.GlobalEnv.rule_ctor_name = ctor_name)
                    info.rec_rules
                with
                | None -> None
                | Some rule ->
                    let params = List.take info.rec_num_params sp in
                    let motive = List.nth sp info.rec_num_params in
                    let methods_start = info.rec_num_params + 1 in
                    let methods =
                      List.drop methods_start sp
                      |> List.take info.rec_num_methods
                    in
                    let fields = List.drop info.rec_num_params ctor_sp in
                    let method_idx =
                      List.find_index
                        (fun r -> r.GlobalEnv.rule_ctor_name = ctor_name)
                        info.rec_rules
                      |> Option.get
                    in
                    let method_val = List.nth methods method_idx in
                    let app arg fn = do_app genv fn arg in
                    let apps args fn = List.fold_left (do_app genv) fn args in
                    let ihs =
                      List.mapi
                        (fun ih_idx rec_arg_idx ->
                          let field = List.nth fields rec_arg_idx in
                          let rec_indices_for_this =
                            List.nth rule.rule_rec_indices ih_idx
                          in
                          let field_indices =
                            List.map (List.nth fields) rec_indices_for_this
                          in
                          let rec_head =
                            VTmNeutral
                              (HConst (Name.child info.rec_ind_name "rec"), [])
                          in
                          rec_head |> apps params |> app motive |> apps methods
                          |> apps field_indices |> app field)
                        rule.rule_rec_args
                    in
                    Some (method_val |> apps fields |> apps ihs))
            | _ -> None))
  | _ -> None

(* ========== Quoting ========== *)

let rec quote_ty (genv : GlobalEnv.t) (l : int) : vl_ty -> ty = function
  | VTyU -> TyU
  | VTyPi (x, a, ClosTy (env, body)) ->
      let a' = quote_ty genv l a in
      let var = VTmNeutral (HVar (Lvl l), []) in
      let b' = quote_ty genv (l + 1) (eval_ty genv (var :: env) body) in
      TyPi (x, a', b')
  | VTyEl n -> TyEl (quote_neutral genv l n)

and quote_tm (genv : GlobalEnv.t) (l : int) : vl_tm -> tm = function
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

and quote_neutral (genv : GlobalEnv.t) (l : int) ((h, sp) : neutral) : tm =
  let head =
    match h with
    | HVar (Lvl k) -> TmVar (Idx (l - k - 1))
    | HConst name -> TmConst name
    | HSorry (id, ty) -> TmSorry (id, quote_ty genv l ty)
  in
  quote_spine genv l head sp

and quote_spine (genv : GlobalEnv.t) (l : int) (head : tm) : spine -> tm =
  function
  | [] -> head
  | arg :: sp -> quote_spine genv l (TmApp (head, quote_tm genv l arg)) sp

(* Convert a value type to a term representing its code *)
and reify_ty (genv : GlobalEnv.t) (l : int) : vl_ty -> tm = function
  | VTyU -> raise (Elab_error "Cannot reify Type as a term")
  | VTyPi (x, a, ClosTy (env, b)) ->
      let var = VTmNeutral (HVar (Lvl l), []) in
      let a' = reify_ty genv l a in
      let b_ty = eval_ty genv (var :: env) b in
      let b' = reify_ty genv (l + 1) b_ty in
      TmPiHat (x, a', b')
  | VTyEl n -> quote_neutral genv l n

(* ========== Conversion ========== *)

let rec conv_ty (genv : GlobalEnv.t) (l : int) : vl_ty * vl_ty -> bool =
  function
  | VTyU, VTyU -> true
  | VTyPi (_, a1, ClosTy (env1, b1)), VTyPi (_, a2, ClosTy (env2, b2)) ->
      conv_ty genv l (a1, a2)
      &&
      let var = VTmNeutral (HVar (Lvl l), []) in
      conv_ty genv (l + 1)
        (eval_ty genv (var :: env1) b1, eval_ty genv (var :: env2) b2)
  | VTyEl n1, VTyEl n2 -> conv_neutral genv l (n1, n2)
  | _ -> false

and conv_tm (genv : GlobalEnv.t) (l : int) : vl_tm * vl_tm -> bool = function
  | VTmNeutral n1, VTmNeutral n2 ->
      conv_neutral genv l (n1, n2)
      || try_eta_struct genv l n1 (VTmNeutral n1)
      || try_eta_struct genv l n2 (VTmNeutral n2)
  | VTmLam (_, _, ClosTm (env1, body1)), VTmLam (_, _, ClosTm (env2, body2)) ->
      let var = VTmNeutral (HVar (Lvl l), []) in
      conv_tm genv (l + 1)
        (eval_tm genv (var :: env1) body1, eval_tm genv (var :: env2) body2)
  | VTmPiHat (_, a1, ClosTm (env1, b1)), VTmPiHat (_, a2, ClosTm (env2, b2)) ->
      conv_tm genv l (a1, a2)
      &&
      let var = VTmNeutral (HVar (Lvl l), []) in
      conv_tm genv (l + 1)
        (eval_tm genv (var :: env1) b1, eval_tm genv (var :: env2) b2)
  | _ -> false

and try_eta_struct (genv : GlobalEnv.t) (l : int) (ctor_app : neutral)
    (other : vl_tm) : bool =
  match ctor_app with
  | HConst ctor_name, sp -> (
      match GlobalEnv.find_constructor ctor_name genv with
      | None -> false
      | Some info -> (
          let info_opt : GlobalEnv.structure_info option =
            match GlobalEnv.find_structure info.ind_name genv with
            | Some info -> Some info
            | None -> (
                (* Also allow eta for unit-like types *)
                match
                  GlobalEnv.find_recursor (Name.child info.ind_name "rec") genv
                with
                | Some rec_info
                  when rec_info.rec_num_indices = 0
                       && List.length rec_info.rec_rules = 1 ->
                    let rule = List.hd rec_info.rec_rules in
                    if
                      rule.rule_rec_args = [] && rule.rule_nfields = 0
                      && Name.equal rule.rule_ctor_name ctor_name
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
                        match GlobalEnv.find_tm proj_name genv with
                        | Some proj_fn ->
                            let with_params =
                              List.fold_left (do_app genv) proj_fn params
                            in
                            do_app genv with_params other
                        | None -> VTmNeutral (HConst proj_name, [])
                      in
                      conv_tm genv l (field, proj_result)
                      && check_fields (fname_rest, field_rest)
                  | _ -> false
                in
                check_fields (info.struct_field_names, fields)))
  | _, _ -> false

and conv_neutral (genv : GlobalEnv.t) (l : int)
    (((h1, sp1), (h2, sp2)) : neutral * neutral) : bool =
  conv_head (h1, h2) && conv_spine genv l (sp1, sp2)

and conv_head : head * head -> bool = function
  | HVar l1, HVar l2 -> l1 = l2
  | HConst n1, HConst n2 -> Name.equal n1 n2
  | HSorry (id1, _), HSorry (id2, _) -> id1 = id2
  | _, _ -> false

and conv_spine (genv : GlobalEnv.t) (l : int) : spine * spine -> bool = function
  | [], [] -> true
  | a1 :: sp1', a2 :: sp2' ->
      conv_tm genv l (a1, a2) && conv_spine genv l (sp1', sp2')
  | _, _ -> false

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
      | { name = Some n; ty } :: _ when String.equal n name -> Some (k, ty)
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

let find_ty (genv : GlobalEnv.t) (name : Name.t) : vl_ty option =
  match GlobalEnv.find_opt name genv with
  | Some (GlobalEnv.Def { ty; _ })
  | Some (GlobalEnv.Opaque { ty })
  | Some (GlobalEnv.Recursor { ty; _ })
  | Some (GlobalEnv.Constructor { ty; _ }) ->
      Some ty
  | Some (GlobalEnv.Inductive { ty; _ }) -> Some (eval_ty genv [] ty)
  | Some (GlobalEnv.Structure { ind = { ty; _ }; _ }) ->
      Some (eval_ty genv [] ty)
  | None -> None

(* ========== Elaboration ========== *)

let rec check_ty (genv : GlobalEnv.t) (ctx : Context.t) : Raw.t -> ty = function
  | Raw.U -> TyU
  | Raw.Pi ((names, dom), cod) ->
      let dom' = check_ty genv ctx dom in
      let dom_val = eval_ty genv (Context.env ctx) dom' in
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
      let dom_val = eval_ty genv (Context.env ctx) dom' in
      let ctx' = Context.bind None dom_val ctx in
      let cod' = check_ty genv ctx' cod in
      TyPi (None, dom', cod')
  | Raw.Sigma ((names, fst_ty), snd_ty) ->
      let fst' = check_ty genv ctx fst_ty in
      let fst_val = eval_ty genv (Context.env ctx) fst' in
      let rec bind_all ctx = function
        | [] -> check_ty genv ctx snd_ty
        | name :: rest ->
            let fst_code = reify_ty genv (Context.lvl ctx) fst_val in
            let ctx' = Context.bind name fst_val ctx in
            let snd' = bind_all ctx' rest in
            let snd_val = eval_ty genv (Context.env ctx') snd' in
            let snd_code = reify_ty genv (Context.lvl ctx') snd_val in
            let snd_fn = TmLam (name, TyEl fst_code, snd_code) in
            TyEl
              (TmApp (TmApp (TmConst (Name.parse "Sigma"), fst_code), snd_fn))
      in
      bind_all ctx names
  | Raw.Prod (fst_ty, snd_ty) ->
      let fst' = check_ty genv ctx fst_ty in
      let fst_val = eval_ty genv (Context.env ctx) fst' in
      let fst_code = reify_ty genv (Context.lvl ctx) fst_val in
      let snd' = check_ty genv ctx snd_ty in
      let snd_val = eval_ty genv (Context.env ctx) snd' in
      let snd_code = reify_ty genv (Context.lvl ctx) snd_val in
      TyEl (TmApp (TmApp (TmConst (Name.parse "Prod"), fst_code), snd_code))
  | Raw.Eq (a, b) ->
      let a_tm, a_ty = infer_tm genv ctx a in
      let b_tm, _ = infer_tm genv ctx b in
      let a_ty_tm = reify_ty genv (Context.lvl ctx) a_ty in
      let eq_ty =
        TyEl
          (TmApp (TmApp (TmApp (TmConst (Name.parse "Eq"), a_ty_tm), a_tm), b_tm))
      in
      eq_ty
  | t ->
      let tm, ty_val = infer_tm genv ctx t in
      if not (conv_ty genv (Context.lvl ctx) (ty_val, VTyU)) then
        raise
          (Elab_error
             (Format.asprintf "Expected Type, got %a"
                (Pretty.pp_ty_ctx (Context.names ctx))
                (quote_ty genv (Context.lvl ctx) ty_val)));
      TyEl tm

and infer_tm (genv : GlobalEnv.t) (ctx : Context.t) : Raw.t -> tm * vl_ty =
  function
  | Raw.Ident name -> (
      match Context.lookup_name ctx name with
      | Some (k, ty) -> (TmVar (Idx k), ty)
      | None -> (
          let fqn = Name.parse name in
          match find_ty genv fqn with
          | Some ty -> (TmConst fqn, ty)
          | None ->
              raise (Elab_error (Format.sprintf "Unbound variable: %s" name))))
  | Raw.App (f, a) -> (
      let f', f_ty = infer_tm genv ctx f in
      match f_ty with
      | VTyPi (_, a_ty, ClosTy (env, b_ty)) ->
          let a' = check_tm genv ctx a a_ty in
          let a_val = eval_tm genv (Context.env ctx) a' in
          (TmApp (f', a'), eval_ty genv (a_val :: env) b_ty)
      | _ -> raise (Elab_error "Expected function type in application"))
  | Raw.U -> raise (Elab_error "Cannot infer type of Type")
  | Raw.Ann (e, ty) ->
      let ty' = check_ty genv ctx ty in
      let ty_val = eval_ty genv (Context.env ctx) ty' in
      let e' = check_tm genv ctx e ty_val in
      (e', ty_val)
  | Raw.Lam (binders, body) ->
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
      go ctx binders
  | Raw.Pi ((names, dom), cod) ->
      let dom' = infer_tm genv ctx dom in
      let dom_tm, _ = dom' in
      let dom_val = do_el (eval_tm genv (Context.env ctx) dom_tm) in
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
      let dom_val = do_el (eval_tm genv (Context.env ctx) dom_tm) in
      let ctx' = Context.bind None dom_val ctx in
      let cod_tm, _ = infer_tm genv ctx' cod in
      (TmPiHat (None, dom_tm, cod_tm), VTyU)
  | Raw.Sigma ((names, fst_ty), snd_ty) ->
      let fst_tm, fst_tm_ty = infer_tm genv ctx fst_ty in
      if not (conv_ty genv (Context.lvl ctx) (fst_tm_ty, VTyU)) then
        raise (Elab_error "Expected Type in sigma domain");
      let fst_code_val = eval_tm genv (Context.env ctx) fst_tm in
      let fst_val = do_el fst_code_val in
      let rec bind_all ctx = function
        | [] ->
            let snd_tm, snd_tm_ty = infer_tm genv ctx snd_ty in
            if not (conv_ty genv (Context.lvl ctx) (snd_tm_ty, VTyU)) then
              raise (Elab_error "Expected Type in sigma codomain");
            snd_tm
        | name :: rest ->
            let ctx' = Context.bind name fst_val ctx in
            let snd' = bind_all ctx' rest in
            let fst_tm' = quote_tm genv (Context.lvl ctx) fst_code_val in
            let snd_fn = TmLam (name, TyEl fst_tm', snd') in
            TmApp (TmApp (TmConst (Name.parse "Sigma"), fst_tm'), snd_fn)
      in
      (bind_all ctx names, VTyU)
  | Raw.Prod (fst_ty, snd_ty) ->
      let fst_tm, fst_tm_ty = infer_tm genv ctx fst_ty in
      if not (conv_ty genv (Context.lvl ctx) (fst_tm_ty, VTyU)) then
        raise (Elab_error "Expected Type in product domain");
      let snd_tm, snd_tm_ty = infer_tm genv ctx snd_ty in
      if not (conv_ty genv (Context.lvl ctx) (snd_tm_ty, VTyU)) then
        raise (Elab_error "Expected Type in product codomain");
      (TmApp (TmApp (TmConst (Name.parse "Prod"), fst_tm), snd_tm), VTyU)
  | Raw.Pair (a, b) ->
      let a', a_ty = infer_tm genv ctx a in
      let b', b_ty = infer_tm genv ctx b in
      let a_code = reify_ty genv (Context.lvl ctx) a_ty in
      let b_code = reify_ty genv (Context.lvl ctx) b_ty in
      let prod_code =
        TmApp (TmApp (TmConst (Name.parse "Prod"), a_code), b_code)
      in
      let pair_tm =
        TmApp
          ( TmApp
              ( TmApp
                  ( TmApp (TmConst (Name.child (Name.parse "Prod") "mk"), a_code),
                    b_code ),
                a' ),
            b' )
      in
      let pair_ty = eval_ty genv (Context.env ctx) (TyEl prod_code) in
      (pair_tm, pair_ty)
  | Raw.Proj1 t -> (
      let t', t_ty = infer_tm genv ctx t in
      match t_ty with
      | VTyEl (HConst name, [ a_code_val; b_val ]) ->
          let a_ty = do_el a_code_val in
          let a_code_tm = quote_tm genv (Context.lvl ctx) a_code_val in
          if Name.equal name (Name.parse "Sigma") then
            let b_tm = quote_tm genv (Context.lvl ctx) b_val in
            ( TmApp
                ( TmApp
                    ( TmApp
                        ( TmConst (Name.child (Name.parse "Sigma") "fst"),
                          a_code_tm ),
                      b_tm ),
                  t' ),
              a_ty )
          else if Name.equal name (Name.parse "Prod") then
            let b_code_tm = quote_tm genv (Context.lvl ctx) b_val in
            ( TmApp
                ( TmApp
                    ( TmApp
                        ( TmConst (Name.child (Name.parse "Prod") "fst"),
                          a_code_tm ),
                      b_code_tm ),
                  t' ),
              a_ty )
          else
            raise (Elab_error "Expected sigma/product type in projection")
      | _ -> raise (Elab_error "Expected sigma/product type in projection"))
  | Raw.Proj2 t -> (
      let t', t_ty = infer_tm genv ctx t in
      match t_ty with
      | VTyEl (HConst name, [ a_code_val; b_val ]) ->
          let a_code_tm = quote_tm genv (Context.lvl ctx) a_code_val in
          if Name.equal name (Name.parse "Sigma") then
            let b_tm = quote_tm genv (Context.lvl ctx) b_val in
            let fst_tm =
              TmApp
                ( TmApp
                    ( TmApp
                        ( TmConst (Name.child (Name.parse "Sigma") "fst"),
                          a_code_tm ),
                      b_tm ),
                  t' )
            in
            let fst_val = eval_tm genv (Context.env ctx) fst_tm in
            let snd_ty = do_el (do_app genv b_val fst_val) in
            let snd_tm =
              TmApp
                ( TmApp
                    ( TmApp
                        ( TmConst (Name.child (Name.parse "Sigma") "snd"),
                          a_code_tm ),
                      b_tm ),
                  t' )
            in
            (snd_tm, snd_ty)
          else if Name.equal name (Name.parse "Prod") then
            let b_code_tm = quote_tm genv (Context.lvl ctx) b_val in
            let snd_ty = do_el b_val in
            let snd_tm =
              TmApp
                ( TmApp
                    ( TmApp
                        ( TmConst (Name.child (Name.parse "Prod") "snd"),
                          a_code_tm ),
                      b_code_tm ),
                  t' )
            in
            (snd_tm, snd_ty)
          else
            raise (Elab_error "Expected sigma/product type in projection")
      | _ -> raise (Elab_error "Expected sigma/product type in projection"))
  | Raw.NatLit n ->
      if n < 0 then
        raise (Elab_error "Negative numeric literal")
      else
        let rec nat_raw (n : int) : Raw.t =
          if n = 0 then
            Raw.Ident "Nat.zero"
          else
            Raw.App (Raw.Ident "Nat.succ", nat_raw (n - 1))
        in
        infer_tm genv ctx (nat_raw n)
  | Raw.Add (a, b) ->
      infer_tm genv ctx (Raw.App (Raw.App (Raw.Ident "Nat.add", a), b))
  | Raw.Sub (a, b) ->
      infer_tm genv ctx (Raw.App (Raw.App (Raw.Ident "Nat.sub", a), b))
  | Raw.Eq (a, b) ->
      let a_tm, a_ty = infer_tm genv ctx a in
      let b_tm, _ = infer_tm genv ctx b in
      let a_ty_tm = reify_ty genv (Context.lvl ctx) a_ty in
      ( TmApp (TmApp (TmApp (TmConst (Name.parse "Eq"), a_ty_tm), a_tm), b_tm),
        VTyU )
  | Raw.Let (name, ty_opt, rhs, body) ->
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
  | Raw.Sorry ->
      let id = fresh_sorry_id () in
      let hole_ty =
        VTyEl (HConst (Name.parse (Format.sprintf "?ty%d†" id)), [])
      in
      (TmSorry (id, quote_ty genv (Context.lvl ctx) hole_ty), hole_ty)

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
                    let ann_val = eval_ty genv (Context.env ctx) ann' in
                    if not (conv_ty genv (Context.lvl ctx) (ann_val, a_ty)) then
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
      go ctx expected binders
  | Raw.Pair (a, b), VTyEl (HConst name, [ a_code_val; b_val ]) ->
      if Name.equal name (Name.parse "Sigma") then
        let fst_ty = do_el a_code_val in
        let a' = check_tm genv ctx a fst_ty in
        let a_val = eval_tm genv (Context.env ctx) a' in
        let b_code_val = do_app genv b_val a_val in
        let snd_ty = do_el b_code_val in
        let b' = check_tm genv ctx b snd_ty in
        let a_code_tm = quote_tm genv (Context.lvl ctx) a_code_val in
        let b_tm = quote_tm genv (Context.lvl ctx) b_val in
        TmApp
          ( TmApp
              ( TmApp
                  ( TmApp
                      (TmConst (Name.child (Name.parse "Sigma") "mk"), a_code_tm),
                    b_tm ),
                a' ),
            b' )
      else if Name.equal name (Name.parse "Prod") then
        let fst_ty = do_el a_code_val in
        let snd_ty = do_el b_val in
        let a' = check_tm genv ctx a fst_ty in
        let b' = check_tm genv ctx b snd_ty in
        let a_code_tm = quote_tm genv (Context.lvl ctx) a_code_val in
        let b_code_tm = quote_tm genv (Context.lvl ctx) b_val in
        TmApp
          ( TmApp
              ( TmApp
                  ( TmApp
                      (TmConst (Name.child (Name.parse "Prod") "mk"), a_code_tm),
                    b_code_tm ),
                a' ),
            b' )
      else
        raise (Elab_error "Expected sigma/product type in pair")
  | Raw.Let (name, ty_opt, rhs, body), expected ->
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
  | Raw.Sorry, expected ->
      let id = fresh_sorry_id () in
      TmSorry (id, quote_ty genv (Context.lvl ctx) expected)
  | _ ->
      let tm, inferred = infer_tm genv ctx raw in
      (if not (conv_ty genv (Context.lvl ctx) (inferred, expected)) then
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
  | TmConst name -> Name.equal name ind
  | TmLam (_, a, body) -> has_ind_occ_ty ind a || has_ind_occ_tm ind body
  | TmApp (f, a) -> has_ind_occ_tm ind f || has_ind_occ_tm ind a
  | TmPiHat (_, a, b) -> has_ind_occ_tm ind a || has_ind_occ_tm ind b
  | TmSorry (_, ty) -> has_ind_occ_ty ind ty
  | TmLet (_, ty, t, body) ->
      has_ind_occ_ty ind ty || has_ind_occ_tm ind t || has_ind_occ_tm ind body

let rec is_valid_ind_app (ind : Name.t) : tm -> bool = function
  | TmConst name -> Name.equal name ind
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
let check_inductive_param_positive (genv : GlobalEnv.t) (f_name : Name.t) : bool
    =
  match GlobalEnv.find_inductive f_name genv with
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

let rec check_positivity_ty (genv : GlobalEnv.t) (ind : Name.t) : ty -> unit =
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

and check_positivity_tm (genv : GlobalEnv.t) (ind : Name.t) (tm : tm) : unit =
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
        | Some f_name when Option.is_some (GlobalEnv.find_inductive f_name genv)
          ->
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

let rec check_strict_positivity (genv : GlobalEnv.t) (ind : Name.t) : ty -> unit
    = function
  | TyPi (_, a, b) ->
      check_positivity_ty genv ind a;
      check_strict_positivity genv ind b
  | _ -> ()

let rec check_returns_inductive (ind : Name.t) : ty -> bool = function
  | TyEl (TmConst name) -> Name.equal name ind
  | TyEl (TmApp (f, _)) -> check_returns_inductive_tm ind f
  | TyPi (_, _, b) -> check_returns_inductive ind b
  | _ -> false

and check_returns_inductive_tm (ind : Name.t) : tm -> bool = function
  | TmConst name -> Name.equal name ind
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

let elab_ctor (genv : GlobalEnv.t) (ind : Name.t) (param_ctx : Context.t)
    (param_tys : (string option * ty) list) (num_params : int)
    (ctor : Syntax.Raw.constructor) : Name.t * ty * vl_ty =
  let full_name = Name.child ind ctor.name in
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
  let ctor_body = build_ctor_body param_ctx 0 ctor.params in
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
  | TyEl (TmConst name) -> Name.equal name ind
  | TyEl (TmApp (f, _)) -> is_recursive_arg_tm ind f
  | TyPi (_, _, b) -> is_recursive_arg_ty ind b
  | _ -> false

and is_recursive_arg_tm (ind : Name.t) : tm -> bool = function
  | TmConst name -> Name.equal name ind
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
    | TmConst name when Name.equal name ind -> acc
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
let gen_recursor_ty (genv : GlobalEnv.t) (ind : Name.t) (num_params : int)
    (param_tys : (string option * ty) list)
    (index_tys : (string option * ty) list) (ctor_tys : (Name.t * ty) list) :
    vl_ty =
  let app arg fn = do_app genv fn arg in
  let apps args fn = List.fold_left (do_app genv) fn args in

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
          mk_pi lvl env (Some "x") x_ty (fun _x -> VTyU)
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
                    (nested_order : vl_tm list) :
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
                        |> app (field_var |> apps (List.rev nested_order)))
                  | (n, ty) :: rest ->
                      let dom =
                        eval_ty genv (nested_rev @ prefix_rev @ params_rev) ty
                      in
                      mk_pi lvl env n dom (fun v ->
                          mk_ih_ty (lvl + 1) (v :: env) (v :: nested_rev)
                            (nested_order @ [ v ]) rest)
                in

                let ih_ty = mk_ih_ty outer_lvl outer_env [] [] nested_binders in
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
                  mk_pi lvl env (Some "x") x_ty (fun x ->
                      let motive_app = motive |> apps indices_order in
                      do_el (do_app genv motive_app x))
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

let elab_inductive (genv : GlobalEnv.t) (ind_str : string)
    (raw_params : Raw.binder_group list) (ind_ty_opt : Raw.t option)
    (ctors : Syntax.Raw.constructor list) : GlobalEnv.t * (Name.t * ty) list =
  let ind = Name.parse ind_str in
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
  let param_ctx, param_tys = elab_params Context.empty [] raw_params in
  let num_params = List.length param_tys in
  let result_ty =
    match ind_ty_opt with
    | None -> TyU
    | Some ty_raw -> check_ty genv param_ctx ty_raw
  in
  let ty =
    List.fold_right
      (fun (name, ty) body -> TyPi (name, ty, body))
      param_tys result_ty
  in
  let ind_ty_val = eval_ty genv [] ty in
  let genv = NameMap.add ind (GlobalEnv.Opaque { ty = ind_ty_val }) genv in
  let ctor_results =
    List.map (elab_ctor genv ind param_ctx param_tys num_params) ctors
  in
  let genv =
    List.fold_left
      (fun g (ctor_idx, (name, _ty, ty_val)) ->
        NameMap.add name
          (GlobalEnv.Constructor { ty = ty_val; ind_name = ind; ctor_idx })
          g)
      genv
      (List.mapi (fun i x -> (i, x)) ctor_results)
  in
  let ctor_name_tys = List.map (fun (name, ty, _) -> (name, ty)) ctor_results in
  let genv =
    NameMap.add ind (GlobalEnv.Inductive { ty; ctors = ctor_name_tys }) genv
  in
  let rec_name = Name.child ind "rec" in
  let index_tys = extract_indices result_ty in
  let num_indices = List.length index_tys in
  let rec_ty_val =
    gen_recursor_ty genv ind num_params param_tys index_tys ctor_name_tys
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
              let is_rec = is_recursive_arg_ty ind arg_ty in
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
          if num_indices = 0 then
            List.map (fun _ -> []) rec_args
          else
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
        GlobalEnv.
          {
            rule_ctor_name = ctor_name;
            rule_nfields = nfields;
            rule_rec_args = rec_args;
            rule_rec_indices = rec_indices;
          })
      ctor_name_tys
  in
  let rec_info : GlobalEnv.recursor_info =
    {
      ty = rec_ty_val;
      rec_ind_name = ind;
      rec_num_params = num_params;
      rec_num_indices = num_indices;
      rec_num_motives = 1;
      rec_num_methods = List.length ctor_name_tys;
      rec_rules;
    }
  in
  let genv = NameMap.add rec_name (GlobalEnv.Recursor rec_info) genv in
  let rec_ty = quote_ty genv 0 rec_ty_val in
  (genv, ((ind, ty) :: ctor_name_tys) @ [ (rec_name, rec_ty) ])

(* ========== Program Elaboration ========== *)

exception Circular_import of Module_name.t
exception Import_not_found of Module_name.t

let elab_program_with_imports ~(root : string) ~(read_file : string -> string)
    ~(parse : string -> Raw.program) (prog : Raw.program) :
    (Name.t * tm * ty) list =
  let rec process_import genv imported importing m =
    if List.exists (Module_name.equal m) importing then
      raise (Circular_import m);
    if ModuleSet.mem m imported then
      (genv, imported)
    else
      let path = Module_name.to_path root m in
      let content =
        try read_file path with
        | _ -> raise (Import_not_found m)
      in
      let imported_prog = parse content in
      let genv, imported, _ =
        go genv imported (m :: importing) [] imported_prog
      in
      (genv, ModuleSet.add m imported)
  and go genv imported importing acc = function
    | [] -> (genv, imported, List.rev acc)
    | Raw.Import { module_name } :: rest ->
        let m = Module_name.parse module_name in
        let genv, imported = process_import genv imported importing m in
        go genv imported importing acc rest
    | Raw.Def { name; body } :: rest ->
        let full_name = Name.parse name in
        let term, ty_val = infer_tm genv Context.empty body in
        let term_val = eval_tm genv [] term in
        let genv =
          NameMap.add full_name
            (GlobalEnv.Def { ty = ty_val; tm = term_val })
            genv
        in
        let ty_out = quote_ty genv 0 ty_val in
        go genv imported importing ((full_name, term, ty_out) :: acc) rest
    | Raw.Example { body } :: rest ->
        let _ = infer_tm genv Context.empty body in
        go genv imported importing acc rest
    | Raw.Inductive { name; params; ty; ctors } :: rest ->
        let genv, results = elab_inductive genv name params ty ctors in
        let acc =
          List.fold_left
            (fun acc (n, ty) -> (n, TmConst n, ty) :: acc)
            acc results
        in
        go genv imported importing acc rest
    | Raw.Structure { name; params; ty; fields } :: rest ->
        let fields : Syntax.Raw.field list = fields in
        let () =
          match ty with
          | None -> ()
          | Some Raw.U -> ()
          | Some _ -> raise (Elab_error "Structure result type must be Type")
        in
        let mk_field_ty (field : Syntax.Raw.field) : Raw.t =
          List.fold_right
            (fun bg body -> Raw.Pi (bg, body))
            field.binders field.ty
        in
        let ctor_binders =
          List.map
            (fun (field : Syntax.Raw.field) ->
              (Some field.name, Some (mk_field_ty field)))
            fields
        in
        let ctors : Syntax.Raw.constructor list =
          [ { name = "mk"; params = ctor_binders; ty = None } ]
        in
        let genv, results = elab_inductive genv name params ty ctors in
        let ind_name = Name.parse name in
        let struct_info : GlobalEnv.structure_info =
          {
            struct_ind_name = ind_name;
            struct_ctor_name = Name.child ind_name "mk";
            struct_num_params =
              List.fold_left
                (fun n ((ns, _) : Raw.binder_group) -> n + List.length ns)
                0 params;
            struct_num_fields = List.length fields;
            struct_field_names =
              List.map (fun (field : Syntax.Raw.field) -> field.name) fields;
          }
        in
        let genv =
          match GlobalEnv.find_opt ind_name genv with
          | Some (GlobalEnv.Inductive ind) ->
              NameMap.add ind_name
                (GlobalEnv.Structure { ind; info = struct_info })
                genv
          | _ -> genv
        in
        let acc =
          List.fold_left
            (fun acc (n, ty) -> (n, TmConst n, ty) :: acc)
            acc results
        in
        let param_names =
          List.concat_map (fun ((ns, _) : Raw.binder_group) -> ns) params
        in
        let struct_app =
          List.fold_left
            (fun acc -> function
              | Some n -> Raw.App (acc, Raw.Ident n)
              | None -> acc)
            (Raw.Ident name) param_names
        in
        let make_proj_app fname =
          let base =
            List.fold_left
              (fun acc -> function
                | Some n -> Raw.App (acc, Raw.Ident n)
                | None -> acc)
              (Raw.Ident (name ^ "." ^ fname))
              param_names
          in
          Raw.App (base, Raw.Ident "s")
        in
        let rec subst_fields ef = function
          | Raw.Ident x -> (
              match List.assoc_opt x ef with
              | Some proj -> proj
              | None -> Raw.Ident x)
          | Raw.App (f, a) -> Raw.App (subst_fields ef f, subst_fields ef a)
          | Raw.Lam (bs, body) ->
              let bound = List.filter_map fst bs in
              let earlier_fields' =
                List.filter (fun (n, _) -> not (List.mem n bound)) ef
              in
              Raw.Lam
                ( List.map
                    (fun (n, ty) -> (n, Option.map (subst_fields ef) ty))
                    bs,
                  subst_fields earlier_fields' body )
          | Raw.Pi ((ns, ty), body) ->
              let bound = List.filter_map Fun.id ns in
              let earlier_fields' =
                List.filter (fun (n, _) -> not (List.mem n bound)) ef
              in
              Raw.Pi
                ((ns, subst_fields ef ty), subst_fields earlier_fields' body)
          | Raw.Arrow (a, b) -> Raw.Arrow (subst_fields ef a, subst_fields ef b)
          | Raw.Prod (a, b) -> Raw.Prod (subst_fields ef a, subst_fields ef b)
          | Raw.Pair (a, b) -> Raw.Pair (subst_fields ef a, subst_fields ef b)
          | Raw.Proj1 t -> Raw.Proj1 (subst_fields ef t)
          | Raw.Proj2 t -> Raw.Proj2 (subst_fields ef t)
          | Raw.Eq (a, b) -> Raw.Eq (subst_fields ef a, subst_fields ef b)
          | Raw.Add (a, b) -> Raw.Add (subst_fields ef a, subst_fields ef b)
          | Raw.Sub (a, b) -> Raw.Sub (subst_fields ef a, subst_fields ef b)
          | Raw.Sigma ((ns, a), b) ->
              let bound = List.filter_map Fun.id ns in
              let earlier_fields' =
                List.filter (fun (n, _) -> not (List.mem n bound)) ef
              in
              Raw.Sigma ((ns, subst_fields ef a), subst_fields earlier_fields' b)
          | Raw.Ann (t, ty) -> Raw.Ann (subst_fields ef t, subst_fields ef ty)
          | Raw.Let (n, ty_opt, t, b) ->
              let earlier_fields' = List.filter (fun (x, _) -> x <> n) ef in
              Raw.Let
                ( n,
                  Option.map (subst_fields ef) ty_opt,
                  subst_fields ef t,
                  subst_fields earlier_fields' b )
          | tm -> tm
        in
        let rec_app =
          List.fold_left
            (fun acc -> function
              | Some n -> Raw.App (acc, Raw.Ident n)
              | None -> acc)
            (Raw.Ident (name ^ ".rec"))
            param_names
        in
        let field_binders =
          List.map
            (fun (field : Syntax.Raw.field) -> (Some field.name, None))
            fields
        in
        let param_binders =
          List.concat_map
            (fun ((names, ty) : Raw.binder_group) ->
              List.map (fun n -> (n, Some ty)) names)
            params
        in
        let genv, acc =
          List.fold_left
            (fun (genv, acc) (field : Syntax.Raw.field) ->
              let proj_name = Name.child (Name.parse name) field.name in
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
                        (fun (field : Syntax.Raw.field) -> field.name)
                        fields))
                  field_ty
              in
              let body =
                Raw.Lam
                  ( [ (Some "s", Some struct_app) ],
                    Raw.Ann
                      ( Raw.App
                          ( Raw.App
                              ( Raw.App
                                  ( rec_app,
                                    Raw.Lam ([ (Some "s", None) ], subst_fty) ),
                                Raw.Lam (field_binders, Raw.Ident field.name) ),
                            Raw.Ident "s" ),
                        subst_fty ) )
              in
              let full_def =
                if param_binders = [] then
                  body
                else
                  Raw.Lam (param_binders, body)
              in
              let term, ty_val = infer_tm genv Context.empty full_def in
              let term_val = eval_tm genv [] term in
              let genv =
                NameMap.add proj_name
                  (GlobalEnv.Def { ty = ty_val; tm = term_val })
                  genv
              in
              let ty_out = quote_ty genv 0 ty_val in
              (genv, (proj_name, term, ty_out) :: acc))
            (genv, acc) fields
        in
        go genv imported importing acc rest
  in
  let _, _, result = go GlobalEnv.empty ModuleSet.empty [] [] prog in
  result

let elab_program (prog : Raw.program) : (Name.t * tm * ty) list =
  elab_program_with_imports ~root:"."
    ~read_file:(fun _ -> "")
    ~parse:(fun _ -> [])
    prog
