open Syntax
open Frontend
open Core_syntax

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
        let check_ctor_positive =
         fun ({ ty = ctor_ty; ctor_name = _ } : Global.constructor_info) ->
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
        List.for_all check_ctor_positive info.ind_ctors

let rec check_positivity_ty (genv : Global.t) (ind : Name.t) : ty -> unit =
  function
  | TyU -> ()
  | TyPi (_, a, b) ->
      if has_ind_occ_ty ind a then
        Error.raise ~kind:Error.Positivity
          (Format.asprintf "%a has a non-positive occurrence (in domain)"
             Name.pp ind)
          None;
      check_positivity_ty genv ind b
  | TyEl t -> check_positivity_tm genv ind t

and check_positivity_tm (genv : Global.t) (ind : Name.t) (tm : tm) : unit =
  if has_ind_occ_tm ind tm && not (is_valid_ind_app ind tm) then
    match tm with
    | TmVar _ -> ()
    | TmConst _ -> ()
    | TmPiHat (_, a, b) ->
        if has_ind_occ_tm ind a then
          Error.raise ~kind:Error.Positivity
            (Format.asprintf "%a has a non-positive occurrence (in domain)"
               Name.pp ind)
            None;
        check_positivity_tm genv ind b
    | TmApp (_, _) -> (
        match get_app_head tm with
        | Some f_name when Option.is_some (Global.find_inductive f_name genv) ->
            if not (check_inductive_param_positive genv f_name) then
              Error.raise ~kind:Error.Positivity
                (Format.asprintf
                   "%a has a non-positive occurrence (nested in %a)" Name.pp ind
                   Name.pp f_name)
                None
        | _ ->
            Error.raise ~kind:Error.Positivity
              (Format.asprintf "%a has a non-valid occurrence (nested)" Name.pp
                 ind)
              None)
    | TmLam (_, a, body) ->
        check_positivity_ty genv ind a;
        check_positivity_tm genv ind body
    | _ ->
        Error.raise ~kind:Error.Positivity
          (Format.asprintf "%a has a non-valid occurrence" Name.pp ind)
          None

let rec check_strict_positivity (genv : Global.t) (ind : Name.t) : ty -> unit =
  function
  | TyPi (_, a, b) ->
      check_positivity_ty genv ind a;
      check_strict_positivity genv ind b
  | TyU -> ()
  | TyEl _ -> () (* TODO *)

let rec check_returns_inductive_tm (ind : Name.t) : tm -> bool = function
  | TmConst name -> name = ind
  | TmApp (f, _) -> check_returns_inductive_tm ind f
  | _ -> false

let rec check_returns_inductive (ind : Name.t) : ty -> bool = function
  | TyEl tm -> check_returns_inductive_tm ind tm
  | TyPi (_, _, b) -> check_returns_inductive ind b
  | TyU -> false

let check_return_params (ctor_name : Name.t) (ind : Name.t) (nparams : int)
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
      if head = TmConst ind && List.length args < nparams then
        Error.raise ~kind:Error.Positivity
          (Format.asprintf "%a: return type must apply %a to all parameters"
             Name.pp ctor_name Name.pp ind)
          None

(* ========== Inductive Types ========== *)

let fresh_name used =
  let used = List.sort_uniq String.compare used in
  let rec aux n acc =
    let c = Char.chr (Char.code 'a' + (n mod 26)) in
    let n' = (n / 26) - 1 in
    if n' < 0 then
      c :: acc
    else
      aux n' (c :: acc)
  in
  let rec find i =
    let name = String.of_seq (List.to_seq (aux i [])) in
    if List.mem name used then
      find (i + 1)
    else
      name
  in
  find 0

let assign_fresh_names : ty -> ty =
  let rec go used = function
    | TyPi (Some name, a, b) -> TyPi (Some name, a, go (name :: used) b)
    | TyPi (None, a, b) ->
        let name = fresh_name used in
        TyPi (Some name, a, go (name :: used) b)
    | TyU -> TyU
    | TyEl t -> TyEl t
  in
  go []

let elab_ctor (genv : Global.t) (ind_name : Name.t) (param_ctx : Context.t)
    (param_tys : (string option * ty) list) (nparams : int)
    (ctor : Ast.Command.inductive_constructor) : Global.constructor_info * ty =
  let ctor_name = Name.child ind_name ctor.name in
  let field_ctx, field_tys_rev =
    List.fold_left
      (fun (ctx, acc) (_src, name, ty_raw) ->
        let ty = Bidir.check_ty genv ctx ty_raw in
        let ty_val = Nbe.eval_ty genv ctx.env ty in
        let ctx = Context.bind name ty_val ctx in
        (ctx, (name, ty) :: acc))
      (param_ctx, []) ctor.params
  in
  let field_tys = List.rev field_tys_rev in
  let ret_ty : ty =
    match ctor.ty_opt with
    | Some ret_raw ->
        let ret_ty = Bidir.check_ty genv field_ctx ret_raw in
        if not (check_returns_inductive ind_name ret_ty) then
          Error.raise ~kind:Error.Positivity
            (Format.asprintf "%a must return %a" Name.pp ctor_name Name.pp
               ind_name)
            None;
        ret_ty
    | None -> TyEl (TmConst ind_name |-- vars nparams (List.length ctor.params))
  in
  let ctor_fields_ty = field_tys @--> assign_fresh_names ret_ty in

  check_return_params ctor_name ind_name nparams ctor_fields_ty;
  let ty = param_tys @--> ctor_fields_ty in
  check_strict_positivity genv ind_name ty;
  ({ ctor_name; ty }, ctor_fields_ty)

(* ========== Recursor Generation ========== *)

let rec is_recursive_arg_tm (ind : Name.t) : tm -> bool = function
  | TmConst name -> name = ind
  | TmApp (f, _) -> is_recursive_arg_tm ind f
  | _ -> false

let rec is_recursive_arg_ty (ind : Name.t) : ty -> bool = function
  | TyU -> false
  | TyPi (_, _, b) -> is_recursive_arg_ty ind b
  | TyEl tm -> is_recursive_arg_tm ind tm

let elab_inductive (genv : Global.t) (ind : Ast.Command.inductive) : Global.t =
  (* Vector *)
  let ind_name = Name.parse ind.name in
  (* [A : Type], [("a", Type)] *)
  let param_ctx, param_tys = Params.elab_params genv ind.params in
  (* 1 *)
  let nparams = List.length param_tys in
  (* A : Type |- (Nat -> Type) is a well formed type *)
  let result_ty =
    match ind.ty_opt with
    | None -> TyU (* Default to Type *)
    | Some ty_raw -> Bidir.check_ty genv param_ctx ty_raw
  in
  (* (A : Type) -> Nat -> Type *)
  let ty = param_tys @--> result_ty in
  (* Vector : (A : Type) -> (n : Nat) -> Type *)
  (* Temporarily add as opaque *)
  let genv = Global.add ind_name (Global.Opaque { ty }) genv in
  let ctor_infos =
    List.map (elab_ctor genv ind_name param_ctx param_tys nparams) ind.ctors
  in
  let ind_ctors = List.map fst ctor_infos in
  let genv =
    List.fold_left
      (fun g (info : Global.constructor_info) ->
        Global.add info.ctor_name (Constructor info) g)
      genv ind_ctors
  in
  let genv = Global.add ind_name (Inductive { ty; ind_ctors }) genv in
  let rec_name = Name.child ind_name "rec" in
  let index_tys =
    let rec go = function
      | TyPi (name, a, b) -> (name, a) :: go b
      | TyU -> []
      | TyEl _ -> failwith "should not happen"
    in
    go result_ty
  in
  let nindices = List.length index_tys in
  let ctor_fields : ty -> (string option * ty * bool) list =
    let rec go acc = function
      | TyPi (name, arg_ty, rest) ->
          go ((name, arg_ty, is_recursive_arg_ty ind_name arg_ty) :: acc) rest
      | _ -> List.rev acc
    in
    go []
  in

  let extract_index_args (tm : tm) : tm list =
    let rec go acc = function
      | TmConst name when name = ind_name -> acc
      | TmApp (f, a) -> go (a :: acc) f
      | _ -> []
    in
    List.drop nparams (go [] tm)
  in

  let rec indices_in_ty : ty -> tm list = function
    | TyPi (_, _, b) -> indices_in_ty b
    | TyEl tm -> extract_index_args tm
    | _ -> []
  in

  let nmethods = List.length ctor_infos in

  let index_tys =
    List.mapi
      (fun i (name_opt, ty) ->
        match name_opt with
        | Some name -> (Some name, ty)
        | None -> (Some (Format.sprintf "a%d†" i), ty))
      index_tys
  in
  let build_method_ty (ctor_name : Name.t) (ctor_fields_ty : ty) : ty =
    let fields = ctor_fields ctor_fields_ty in
    let nfields = List.length fields in
    let rec_field_infos =
      List.filter_map
        (fun (i, (name, field_ty, is_rec)) ->
          if is_rec then
            Some (i, name, field_ty)
          else
            None)
        (List.mapi (fun i x -> (i, x)) fields)
    in
    let nrec_fields = List.length rec_field_infos in
    let ih_infos =
      List.mapi
        (fun nth_rec_field (nth_field, name, field_ty) ->
          let nested_binders, rec_indices =
            let rec go acc = function
              | TyPi (name, arg_ty, body) -> go ((name, arg_ty) :: acc) body
              | TyEl tm -> (List.rev acc, extract_index_args tm)
              | _ -> (List.rev acc, [])
            in
            go [] field_ty
          in
          let nb = List.length nested_binders in
          let added_fields = nfields - nth_field in
          let ih_body_ty =
            TyEl
              (TmVar (Idx (nb + nfields))
              |-- List.map
                    (fun t ->
                      t |> shift_tm added_fields nb |> shift_tm 1 (nb + nfields))
                    rec_indices
              |- (TmVar (Idx (nb + nfields - 1 - nth_field)) |-- vars nb 0))
          in
          let ih_ty_base =
            List.mapi
              (fun i (name, ty) ->
                (name, ty |> shift_ty added_fields i |> shift_ty 1 (i + nfields)))
              nested_binders
            @--> ih_body_ty
          in
          ( Option.map (Format.sprintf "%s_ih") name,
            shift_ty nth_rec_field 0 ih_ty_base ))
        rec_field_infos
    in
    List.mapi
      (fun i (name, field_ty, _is_rec) -> (name, shift_ty 1 i field_ty))
      fields
    @--> ih_infos
    @--> shift_ty nrec_fields 0
           (TyEl
              (TmVar (Idx nfields)
              |-- List.map (shift_tm 1 nfields) (indices_in_ty ctor_fields_ty)
              |- (TmConst ctor_name
                 |-- vars nparams (nfields + 1)
                 |-- vars nfields 0)))
  in

  let rec_ty : ty =
    param_tys (* parameters *)
    @--> ( Some "motive",
           index_tys
           @--> (None, TyEl (TmConst ind_name |-- vars (nparams + nindices) 0))
           @-> TyU )
         (* motive *)
    @-> List.mapi
          (fun i (info, fields_ty) ->
            ( None,
              shift_ty i 0 (build_method_ty info.Global.ctor_name fields_ty) ))
          ctor_infos (* cases *)
    @--> List.mapi
           (fun i (name, idx_ty) -> (name, shift_ty (1 + nmethods) i idx_ty))
           index_tys (* indices*)
    @--> ( None,
           TyEl
             (TmConst ind_name
             |-- vars nparams (nindices + 1 + nmethods)
             |-- vars nindices 0) )
         (* major premise *)
    @-> TyEl (TmVar (Idx (1 + nindices + nmethods)) |-- vars (nindices + 1) 0)
  in
  let rec_rules =
    List.mapi
      (fun method_idx (info, fields_ty) ->
        let fields = ctor_fields fields_ty in
        let nfields = List.length fields in
        let rec_args =
          fields
          |> List.mapi (fun idx (_name, _ty, is_rec) ->
              if is_rec then
                Some idx
              else
                None)
          |> List.filter_map Fun.id
        in
        let rec_index_patterns =
          List.map
            (fun rec_idx ->
              let _name, field_ty, _is_rec = List.nth fields rec_idx in
              ( rec_idx,
                List.filter_map
                  (function
                    | TmVar (Idx i) ->
                        let field_num = rec_idx - 1 - i in
                        if field_num >= 0 && field_num < nfields then
                          Some i
                        else
                          None
                    | _ -> None)
                  (indices_in_ty field_ty) ))
            rec_args
        in
        let rec_head =
          TmConst rec_name |-- vars (nparams + nmethods + 1) nfields
        in
        let rule_rec_rhs =
          TmVar (Idx (nfields + nmethods - 1 - method_idx))
          |-- vars nfields 0
          |-- List.map
                (fun (rec_arg_idx, index_patterns) ->
                  rec_head
                  |-- List.map
                        (fun i -> TmVar (Idx (nfields - rec_arg_idx + i)))
                        index_patterns
                  |- TmVar (Idx (nfields - 1 - rec_arg_idx)))
                rec_index_patterns
        in
        Global.
          {
            rule_ctor_name = info.ctor_name;
            rule_nfields = nfields;
            rule_rec_rhs;
          })
      ctor_infos
  in

  let rec_info : Global.recursor_info =
    {
      ty = rec_ty;
      rec_name;
      rec_num_params = nparams;
      rec_num_indices = nindices;
      rec_rules;
    }
  in
  Global.add rec_name (Global.Recursor rec_info) genv
