open Syntax
open Core_syntax
open Frontend
open Ast

let elab_structure (genv : Global.t) (info : Command.structure) : Global.t =
  let ind_name = Name.parse info.name in
  let () =
    match info.ty_opt with
    | None -> ()
    | Some (U _) -> ()
    | Some t ->
        Error.raise ~kind:Elaboration "Structure result type must be Type"
          (Ast.get_src t)
  in
  let mk_field_ty (field : Command.structure_field) : t =
    List.fold_right
      (fun (_src, name, ty) body -> Pi (field.src, (field.src, name, ty), body))
      field.params field.ty
  in
  let rec code_of_ty : ty -> tm = function
    | TyEl t -> t
    | TyPi (x, a, b) -> TmPiHat (x, code_of_ty a, code_of_ty b)
    | TyU -> failwith "cannot encode Type as a code"
  in
  let rec drop_pis n (ty : ty) : ty =
    match (n, ty) with
    | 0, ty -> ty
    | n, TyPi (_, _, b) -> drop_pis (n - 1) b
    | _ -> failwith "expected function type"
  in
  let rec collect_pis acc : ty -> (string option * ty) list = function
    | TyPi (x, a, b) -> collect_pis ((x, a) :: acc) b
    | _ -> List.rev acc
  in
  let genv =
    Inductive.elab_inductive genv
      {
        src = info.src;
        name = info.name;
        params = info.params;
        ty_opt = info.ty_opt;
        ctors =
          [
            {
              src = info.src;
              name = "mk";
              params =
                List.map
                  (fun (field : Command.structure_field) ->
                    (field.src, Some field.name, mk_field_ty field))
                  info.fields;
              ty_opt = None;
            };
          ];
      }
  in
  let nparams = List.length info.params in
  let struct_fields =
    List.map (fun (field : Command.structure_field) -> field.name) info.fields
  in
  let genv, struct_info =
    match Global.find_inductive ind_name genv with
    | Some ind ->
        let struct_info : Global.structure_info =
          {
            ty = ind.ty;
            struct_ind_name = ind_name;
            struct_ctor_name = Name.child ind_name "mk";
            struct_num_params = nparams;
            struct_fields;
          }
        in
        (Global.add ind_name (Global.Structure struct_info) genv, struct_info)
    | None ->
        ( genv,
          {
            ty = TyU;
            struct_ind_name = ind_name;
            struct_ctor_name = Name.child ind_name "mk";
            struct_num_params = nparams;
            struct_fields;
          } )
  in
  let _param_ctx, param_tys = Params.elab_params genv info.params in
  let mk_ctor =
    match Global.find_constructor struct_info.struct_ctor_name genv with
    | Some info -> info
    | None -> failwith "missing structure constructor"
  in
  let fields_ty = drop_pis nparams mk_ctor.ty in
  let fields = collect_pis [] fields_ty in
  let rec_name = Name.child ind_name "rec" in
  let struct_ty_in_params : ty = TyEl (TmConst ind_name |-- vars nparams 0) in
  let genv =
    List.fold_left
      (fun genv (field_idx, field_name, field_ty) ->
        let proj_name = Name.child ind_name field_name in
        let prev_fields = List.take field_idx fields in
        let prev_proj_terms =
          List.init field_idx (fun j ->
              TmConst (Name.child ind_name (List.nth struct_fields j))
              |-- vars nparams 1 |- TmVar (Idx 0))
        in
        let field_code_fn = prev_fields @==> code_of_ty field_ty in
        let code_body = shift_tm 1 0 field_code_fn |-- prev_proj_terms in
        let motive_tm = (Some "s", struct_ty_in_params) @=> code_body in
        let method_tm =
          fields @==> TmVar (Idx (List.length fields - 1 - field_idx))
        in
        let proj_tm =
          param_tys
          @==> (TmConst rec_name |-- vars nparams 0 |- motive_tm |- method_tm)
        in
        let proj_ty =
          param_tys @--> (Some "s", struct_ty_in_params) @-> TyEl code_body
        in
        Global.add proj_name
          (Global.Definition { ty = proj_ty; tm = proj_tm })
          genv)
      genv
      (List.mapi
         (fun i (field : Command.structure_field) ->
           let _name_opt, ty = List.nth fields i in
           (i, field.name, ty))
         info.fields)
  in
  genv
