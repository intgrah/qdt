open Syntax
open Frontend

let elab_structure (genv : Global.t) (info : Ast.Command.structure) :
    Global.t * (Name.t * tm * ty) list =
  let ind_name = Name.parse info.name in
  let () =
    match info.ty_opt with
    | None -> ()
    | Some (Ast.U _) -> ()
    | Some _ -> raise (Failure "Structure result type must be Type")
  in
  let mk_field_ty (field : Ast.Command.structure_field) : Ast.t =
    List.fold_right
      (fun (_src, name, ty) body ->
        Ast.Pi (field.src, (field.src, name, ty), body))
      field.params field.ty
  in
  let ctor_binders : Ast.typed_binder list =
    List.map
      (fun (field : Ast.Command.structure_field) ->
        (field.src, Some field.name, mk_field_ty field))
      info.fields
  in
  let ctors : Ast.Command.inductive_constructor list =
    [ { src = info.src; name = "mk"; params = ctor_binders; ty_opt = None } ]
  in
  let genv, results =
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
          (fun (field : Ast.Command.structure_field) -> field.name)
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
  let make_proj_app fname : Ast.t =
    let base =
      List.fold_left
        (fun acc -> function
          | Some n -> Ast.App (None, acc, Ast.Ident (None, n))
          | None -> acc)
        (Ast.Ident (None, info.name ^ "." ^ fname))
        param_names
    in
    Ast.App (None, base, Ast.Ident (None, "s"))
  in
  let rec subst_fields ef : Ast.t -> Ast.t = function
    | Ast.Ident (_, x) -> (
        match List.assoc_opt x ef with
        | Some proj -> proj
        | None -> Ast.Ident (None, x))
    | Ast.App (_, f, a) -> Ast.App (None, subst_fields ef f, subst_fields ef a)
    | Ast.Lam (_, binder, body) ->
        let name =
          match binder with
          | Ast.Untyped (_, name)
          | Ast.Typed (_, name, _) ->
              name
        in
        let earlier_fields' =
          List.filter (fun (n, _) -> not (Some n = name)) ef
        in
        let binder' =
          match binder with
          | Ast.Untyped (src, name) -> Ast.Untyped (src, name)
          | Ast.Typed (src, name, ty) ->
              Ast.Typed (src, name, subst_fields ef ty)
        in
        Ast.Lam (None, binder', subst_fields earlier_fields' body)
    | Ast.Pi (src, (src_binder, name, ty), body) ->
        let earlier_fields' =
          List.filter (fun (n, _) -> not (Some n = name)) ef
        in
        Ast.Pi
          ( src,
            (src_binder, name, subst_fields ef ty),
            subst_fields earlier_fields' body )
    | Ast.Pair (_, a, b) -> Ast.Pair (None, subst_fields ef a, subst_fields ef b)
    | Ast.Eq (_, a, b) -> Ast.Eq (None, subst_fields ef a, subst_fields ef b)
    | Ast.Ann (_, t, ty) -> Ast.Ann (None, subst_fields ef t, subst_fields ef ty)
    | Ast.Let (_, n, ty_opt, t, b) ->
        let earlier_fields' = List.filter (fun (x, _) -> x <> n) ef in
        Ast.Let
          ( None,
            n,
            Option.map (subst_fields ef) ty_opt,
            subst_fields ef t,
            subst_fields earlier_fields' b )
    | tm -> tm
  in
  let rec_app =
    List.fold_left
      (fun acc -> function
        | Some n -> Ast.App (None, acc, Ast.Ident (None, n))
        | None -> acc)
      (Ast.Ident (None, info.name ^ ".rec"))
      param_names
  in
  let field_binders : Ast.binder list =
    List.map
      (fun (field : Ast.Command.structure_field) ->
        Ast.Untyped (None, Some field.name))
      info.fields
  in
  let param_binders : Ast.binder list =
    List.map (fun binder -> Ast.Typed binder) info.params
  in
  let genv, results =
    List.fold_left
      (fun (genv, acc) (field : Ast.Command.structure_field) ->
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
                  (fun (field : Ast.Command.structure_field) -> field.name)
                  info.fields))
            field_ty
        in
        let body : Ast.t =
          Ast.App
            ( None,
              Ast.App
                ( None,
                  rec_app,
                  Ast.Lam (None, Ast.Untyped (None, Some "s"), subst_fty) ),
              Ast.Lam
                ( None,
                  List.hd field_binders,
                  List.fold_right
                    (fun binder acc -> Ast.Lam (None, binder, acc))
                    (List.tl field_binders)
                    (Ast.Ident (None, field.name)) ) )
        in
        let full_def =
          match param_binders with
          | [] -> body
          | hd :: tl ->
              List.fold_right
                (fun binder acc -> Ast.Lam (None, binder, acc))
                (hd :: tl) body
        in
        let term, ty_val = Bidir.infer_tm genv Context.empty full_def in
        let term_val = Nbe.eval_tm genv [] term in
        let ty_quoted = Quote.quote_ty genv 0 ty_val in
        let genv =
          Global.NameMap.add proj_name
            (Global.Def { ty = ty_quoted; tm = term_val })
            genv
        in
        let ty_out = Quote.quote_ty genv 0 ty_val in
        (genv, (proj_name, term, ty_out) :: acc))
      (genv, results) info.fields
  in
  (genv, results)
