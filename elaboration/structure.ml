open Frontend
open Ast

let elab_structure (genv : Global.t) (info : Command.structure) : Global.t =
  let ind_name = Name.parse info.name in
  let () =
    match info.ty_opt with
    | None -> ()
    | Some (U _) -> ()
    | Some _ -> raise (Failure "Structure result type must be Type")
  in
  let mk_field_ty (field : Command.structure_field) : t =
    List.fold_right
      (fun (_src, name, ty) body -> Pi (field.src, (field.src, name, ty), body))
      field.params field.ty
  in
  let ctor_binders : typed_binder list =
    List.map
      (fun (field : Command.structure_field) ->
        (field.src, Some field.name, mk_field_ty field))
      info.fields
  in
  let ctors : Command.inductive_constructor list =
    [ { src = info.src; name = "mk"; params = ctor_binders; ty_opt = None } ]
  in
  let genv =
    Inductive.elab_inductive genv
      {
        src = info.src;
        name = info.name;
        params = info.params;
        ty_opt = info.ty_opt;
        ctors;
      }
  in
  let params = List.map (fun (_src, name, _ty) -> name) info.params in
  let struct_info : Global.structure_info =
    {
      struct_ind_name = ind_name;
      struct_ctor_name = Name.child ind_name "mk";
      struct_num_params = List.length info.params;
      struct_num_fields = List.length info.fields;
      struct_field_names =
        List.map
          (fun (field : Command.structure_field) -> field.name)
          info.fields;
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
  let param_names = params in
  let make_proj_app fname : t =
    let base =
      List.fold_left
        (fun acc -> function
          | Some n -> App (None, acc, Ident (None, n))
          | None -> acc)
        (Ident (None, info.name ^ "." ^ fname))
        param_names
    in
    App (None, base, Ident (None, "s"))
  in
  let rec subst_fields ef : t -> t = function
    | Ident (_, x) -> (
        match List.assoc_opt x ef with
        | Some proj -> proj
        | None -> Ident (None, x))
    | App (_, f, a) -> App (None, subst_fields ef f, subst_fields ef a)
    | Lam (_, binder, body) ->
        let name =
          match binder with
          | Untyped (_, name)
          | Typed (_, name, _) ->
              name
        in
        let earlier_fields =
          List.filter (fun (n, _) -> not (Some n = name)) ef
        in
        let binder' =
          match binder with
          | Untyped (src, name) -> Untyped (src, name)
          | Typed (src, name, ty) -> Typed (src, name, subst_fields ef ty)
        in
        Lam (None, binder', subst_fields earlier_fields body)
    | Pi (src, (src_binder, name, ty), body) ->
        let earlier_fields =
          List.filter (fun (n, _) -> not (Some n = name)) ef
        in
        Pi
          ( src,
            (src_binder, name, subst_fields ef ty),
            subst_fields earlier_fields body )
    | Pair (_, a, b) -> Pair (None, subst_fields ef a, subst_fields ef b)
    | Eq (_, a, b) -> Eq (None, subst_fields ef a, subst_fields ef b)
    | Ann (_, t, ty) -> Ann (None, subst_fields ef t, subst_fields ef ty)
    | Let (_, n, ty_opt, t, b) ->
        let earlier_fields = List.filter (fun (x, _) -> x <> n) ef in
        Let
          ( None,
            n,
            Option.map (subst_fields ef) ty_opt,
            subst_fields ef t,
            subst_fields earlier_fields b )
    | tm -> tm
  in
  let rec_app =
    List.fold_left
      (fun acc -> function
        | Some n -> App (None, acc, Ident (None, n))
        | None -> acc)
      (Ident (None, info.name ^ ".rec"))
      param_names
  in
  let field_binders : binder list =
    List.map
      (fun (field : Command.structure_field) -> Untyped (None, Some field.name))
      info.fields
  in
  let param_binders : binder list =
    List.map (fun binder -> Typed binder) info.params
  in
  List.fold_left
    (fun genv (field : Command.structure_field) ->
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
                (fun (field : Command.structure_field) -> field.name)
                info.fields))
          field_ty
      in
      let body : t =
        App
          ( None,
            App (None, rec_app, Lam (None, Untyped (None, Some "s"), subst_fty)),
            Lam
              ( None,
                List.hd field_binders,
                List.fold_right
                  (fun binder acc -> Lam (None, binder, acc))
                  (List.tl field_binders)
                  (Ident (None, field.name)) ) )
      in
      let full_def =
        match param_binders with
        | [] -> body
        | hd :: tl ->
            List.fold_right
              (fun binder acc -> Lam (None, binder, acc))
              (hd :: tl) body
      in
      let tm, ty_val = Bidir.infer_tm genv Context.empty full_def in
      let ty_quoted = Quote.quote_ty genv 0 ty_val in
      Global.NameMap.add proj_name
        (Global.Definition { ty = ty_quoted; tm })
        genv)
    genv info.fields
