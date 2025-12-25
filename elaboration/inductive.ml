open Frontend
open Syntax
open Nbe

exception Positivity of string

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
          (Positivity
             (Format.asprintf "%a has a non-positive occurrence (in domain)"
                Name.pp ind));
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
            (Positivity
               (Format.asprintf "%a has a non-positive occurrence (in domain)"
                  Name.pp ind));
        check_positivity_tm genv ind b
    | TmApp (_, _) -> (
        match get_app_head tm with
        | Some f_name when Option.is_some (Global.find_inductive f_name genv) ->
            if not (check_inductive_param_positive genv f_name) then
              raise
                (Positivity
                   (Format.asprintf
                      "%a has a non-positive occurrence (nested in %a)" Name.pp
                      ind Name.pp f_name))
        | _ ->
            raise
              (Positivity
                 (Format.asprintf "%a has a non-valid occurrence (nested)"
                    Name.pp ind)))
    | TmLam (_, a, body) ->
        check_positivity_ty genv ind a;
        check_positivity_tm genv ind body
    | _ ->
        raise
          (Positivity
             (Format.asprintf "%a has a non-valid occurrence" Name.pp ind))

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
          (Positivity
             (Format.asprintf "%a: return type must apply %a to all parameters"
                Name.pp ctor_name Name.pp ind))

(* ========== Inductive Types ========== *)

let elab_ctor (genv : Global.t) (ind : Name.t) (param_ctx : Context.t)
    (param_tys : (string option * ty) list) (num_params : int)
    (ctor : Raw_syntax.constructor) : Name.t * ty =
  let full_name = Name.child ind ctor.name in

  let rec build_ctor_body ctx depth = function
    | [] -> (
        match ctor.ty_opt with
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
            let ret_ty = Bidir.check_ty genv ctx ret_raw in
            if not (check_returns_inductive ind ret_ty) then
              raise
                (Positivity
                   (Format.asprintf "%a must return %a" Name.pp full_name
                      Name.pp ind));
            check_return_params full_name ind num_params ret_ty;
            ret_ty)
    | (name, ty) :: rest ->
        let param_ty = Bidir.check_ty genv ctx ty in
        let param_ty_val = eval_ty genv ctx.env param_ty in
        let ctx' = Context.bind name param_ty_val ctx in
        let body_ty = build_ctor_body ctx' (depth + 1) rest in
        TyPi (name, param_ty, body_ty)
  in
  let params = Desugar.desugar_typed_binder_groups ctor.params in
  let ctor_body = build_ctor_body param_ctx 0 params in
  let ctor_ty =
    List.fold_right
      (fun (name, ty) body -> TyPi (name, ty, body))
      param_tys ctor_body
  in
  check_strict_positivity genv ind ctor_ty;
  (full_name, ctor_ty)

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
    let body_ty = Quote.quote_ty genv (lvl + 1) body_val in
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

let elab_params =
  let rec go ctx acc genv = function
    | [] -> (ctx, List.rev acc)
    | (name, ty) :: rest ->
        let ty = Bidir.check_ty genv ctx ty in
        let ty_val = Nbe.eval_ty genv ctx.env ty in
        let ctx = Context.bind name ty_val ctx in
        go ctx ((name, ty) :: acc) genv rest
  in
  go Context.empty []

let elab_inductive (genv : Global.t) (ind : Raw_syntax.inductive_info) :
    Global.t * (Name.t * tm * ty) list =
  let ind_name = Name.parse ind.name in
  let params = Desugar.desugar_typed_binder_groups ind.params in

  let param_ctx, param_tys = elab_params genv params in
  let num_params = List.length param_tys in
  let result_ty =
    match ind.ty_opt with
    | None -> TyU
    | Some ty_raw -> Bidir.check_ty genv param_ctx ty_raw
  in
  let ty =
    List.fold_right
      (fun (name, ty) body -> TyPi (name, ty, body))
      param_tys result_ty
  in
  let genv = Global.NameMap.add ind_name (Global.Opaque { ty }) genv in
  let ctors =
    List.map (elab_ctor genv ind_name param_ctx param_tys num_params) ind.ctors
  in
  let genv =
    List.fold_left
      (fun g (ctor_idx, (name, ty)) ->
        Global.NameMap.add name
          (Global.Constructor { ty; ind_name; ctor_idx })
          g)
      genv
      (List.mapi (fun i x -> (i, x)) ctors)
  in
  let genv =
    Global.NameMap.add ind_name (Global.Inductive { ty; ctors }) genv
  in
  let rec_name = Name.child ind_name "rec" in
  let index_tys = extract_indices result_ty in
  let num_indices = List.length index_tys in
  let rec_ty_val =
    gen_recursor_ty genv ind_name num_params param_tys index_tys ctors
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
              let index_args = List.drop num_params args in
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
      ctors
  in
  let rec_ty = Quote.quote_ty genv 0 rec_ty_val in

  let rec_info : Global.recursor_info =
    {
      ty = rec_ty;
      rec_ind_name = ind_name;
      rec_num_params = num_params;
      rec_num_indices = num_indices;
      rec_num_methods = List.length ctors;
      rec_rules;
    }
  in
  let genv = Global.NameMap.add rec_name (Global.Recursor rec_info) genv in
  let results = (ind_name, ty) :: (rec_name, rec_ty) :: ctors in
  let results' =
    List.fold_left (fun acc (n, ty) -> (n, TmConst n, ty) :: acc) [] results
  in
  (genv, results')
