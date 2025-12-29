open Syntax
open Core_syntax
open Frontend
open Ast

let elab_structure (genv : Global.t) (info : Command.structure) : Global.t =
  let ind_name = Name.parse info.name in
  let result_ty =
    match info.ty_opt with
    | None -> TyU
    | Some (U _) -> TyU
    | Some t ->
        Error.raise ~kind:Elaboration "Structure result type must be Type"
          (Ast.get_src t)
  in
  let rec code_of_ty : ty -> tm = function
    | TyEl t -> t
    | TyPi (x, a, b) -> TmPiHat (x, code_of_ty a, code_of_ty b)
    | TyU -> failwith "cannot encode Type as a code"
  in
  let struct_fields =
    List.map (fun (field : Command.structure_field) -> field.name) info.fields
  in
  let param_ctx, param_tys = Params.elab_params genv info.params in
  let nparams = List.length param_tys in
  let ind_ty : ty = param_tys @--> result_ty in
  let genv = Global.add ind_name (Global.Opaque { ty = ind_ty }) genv in
  let _field_ctx, fields_rev =
    List.fold_left
      (fun (ctx, acc) (field : Command.structure_field) ->
        let field_ctx, field_tys =
          Params.elab_params_from ctx genv field.params
        in
        let ret_ty = Bidir.check_ty genv field_ctx field.ty in
        let field_ty = field_tys @--> ret_ty in
        let field_ty_val = Nbe.eval_ty genv ctx.env field_ty in
        let ctx = Context.bind (Some field.name) field_ty_val ctx in
        (ctx, (Some field.name, field_ty) :: acc))
      (param_ctx, []) info.fields
  in
  let ctor_name = Name.child ind_name "mk" in
  let fields = List.rev fields_rev in
  let ctor_fields_ty : ty =
    fields @--> TyEl (TmConst ind_name |-- vars nparams (List.length fields))
  in
  let genv =
    Inductive.declare_inductive genv ind_name param_tys result_ty
      [ (ctor_name, ctor_fields_ty) ]
  in
  let struct_info : Global.structure_info =
    {
      ty = ind_ty;
      struct_ind_name = ind_name;
      struct_ctor_name = ctor_name;
      struct_num_params = nparams;
      struct_fields;
    }
  in
  let genv = Global.add ind_name (Global.Structure struct_info) genv in
  let rec_name = Name.child ind_name "rec" in
  let struct_ty : ty = TyEl (TmConst ind_name |-- vars nparams 0) in
  let ih_binders : (string option * ty) list =
    List.filter_map
      (fun (name_opt, field_ty) ->
        if Inductive.is_recursive_arg_ty ind_name field_ty then
          Some (Option.map (Format.sprintf "%s_ih") name_opt, TyU)
        else
          None)
      fields
  in
  let rec subst_ty (j : int) (s : tm) : ty -> ty = function
    | TyU -> TyU
    | TyPi (x, a, b) ->
        TyPi (x, subst_ty j s a, subst_ty (j + 1) (shift_tm 1 0 s) b)
    | TyEl t -> TyEl (subst_tm j s t)
  and subst_tm (j : int) (s : tm) : tm -> tm = function
    | TmVar (Idx k) ->
        if k = j then
          s
        else
          TmVar (Idx k)
    | TmConst name -> TmConst name
    | TmLam (x, a, body) ->
        TmLam (x, subst_ty j s a, subst_tm (j + 1) (shift_tm 1 0 s) body)
    | TmApp (f, a) -> TmApp (subst_tm j s f, subst_tm j s a)
    | TmPiHat (x, a, b) ->
        TmPiHat (x, subst_tm j s a, subst_tm (j + 1) (shift_tm 1 0 s) b)
    | TmSorry (id, ty) -> TmSorry (id, subst_ty j s ty)
    | TmLet (x, ty, t, body) ->
        TmLet
          ( x,
            subst_ty j s ty,
            subst_tm j s t,
            subst_tm (j + 1) (shift_tm 1 0 s) body )
  in
  List.fold_left
    (fun genv (field_idx, field_name, field_ty) ->
      let code_body =
        let rec go k acc =
          if k < 0 then
            acc
          else
            let arg =
              shift_tm k 0
                (TmConst (Name.child ind_name (List.nth struct_fields k))
                |-- vars nparams 1 |- TmVar (Idx 0))
            in
            go (k - 1) (shift_tm (-1) 0 (subst_tm 0 (shift_tm 1 0 arg) acc))
        in
        let base = shift_tm 1 field_idx (code_of_ty field_ty) in
        go (field_idx - 1) base
      in
      let proj_tm =
        param_tys
        @==> (TmConst rec_name |-- vars nparams 0
             |- (Some "s", struct_ty) @=> code_body
             |- fields @==> ih_binders
                @==> TmVar
                       (Idx
                          (List.length ih_binders + List.length fields - 1
                         - field_idx)))
      in
      let proj_ty = param_tys @--> (Some "s", struct_ty) @-> TyEl code_body in
      Global.add
        (Name.child ind_name field_name)
        (Global.Definition { ty = proj_ty; tm = proj_tm })
        genv)
    genv
    (List.mapi
       (fun i (field : Command.structure_field) ->
         let _name_opt, ty = List.nth fields i in
         (i, field.name, ty))
       info.fields)
