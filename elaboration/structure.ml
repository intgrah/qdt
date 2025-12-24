open Frontend
open Syntax

let elab_structure (genv : Global.t) (info : Raw_syntax.structure_info) :
    Global.t * (Name.t * tm * ty) list =
  let ind_name = Name.parse info.name in
  let () =
    match info.ty_opt with
    | None -> ()
    | Some Raw_syntax.U -> ()
    | Some _ -> raise (Failure "Structure result type must be Type")
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
    [ { name = "mk"; params = ctor_binders; ty_opt = None } ]
  in
  let genv, results =
    Inductive.elab_inductive genv
      { name = info.name; params = info.params; ty_opt = info.ty_opt; ctors }
  in
  let params = Desugar.desugar_typed_binder_groups info.params in
  let struct_info : Global.structure_info =
    {
      struct_ind_name = ind_name;
      struct_ctor_name = Name.child ind_name "mk";
      struct_num_params = List.length params;
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
  let param_names = List.map fst params in
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
