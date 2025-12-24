open Frontend
open Syntax

exception Elab_error of string

let fresh_sorry_id =
  let counter = ref 0 in
  fun () ->
    let id = !counter in
    incr counter;
    id

let rec check_ty (genv : Global.t) (ctx : Context.t) : Raw_syntax.t -> ty =
  function
  | U -> TyU
  | Pi ((names, dom), cod) ->
      let dom = check_ty genv ctx dom in
      let dom_val = Nbe.eval_ty genv ctx.env dom in
      let dom_ty_at (n : int) : ty =
        Quote.quote_ty genv (ctx.lvl + n) dom_val
      in
      let rec bind_all ctx n = function
        | [] -> check_ty genv ctx cod
        | name :: rest ->
            let ctx' = Context.bind name dom_val ctx in
            let cod' = bind_all ctx' (n + 1) rest in
            TyPi (name, dom_ty_at n, cod')
      in
      bind_all ctx 0 names
  | Arrow (dom, cod) ->
      let dom = check_ty genv ctx dom in
      let dom_val = Nbe.eval_ty genv ctx.env dom in
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
      let a_ty_tm = Quote.reify_ty genv ctx.lvl a_ty in
      let eq_ty =
        TyEl (TmApp (TmApp (TmApp (TmConst [ "Eq" ], a_ty_tm), a_tm), b_tm))
      in
      eq_ty
  | t ->
      let tm, ty_val = infer_tm genv ctx t in
      if not (Nbe.conv_ty genv ctx.lvl ty_val VTyU) then
        raise
          (Elab_error
             (Format.asprintf "Expected Type, got %a"
                (Pretty.pp_ty_ctx (Context.names ctx))
                (Quote.quote_ty genv ctx.lvl ty_val)));
      TyEl tm

and infer_tm (genv : Global.t) (ctx : Context.t) : Raw_syntax.t -> tm * vl_ty =
  function
  | Ident name -> (
      match Context.lookup_name ctx name with
      | Some (k, ty) -> (TmVar (Idx k), ty)
      | None -> (
          let fqn = Name.parse name in
          match Global.find_ty fqn genv with
          | Some ty -> (TmConst fqn, Nbe.eval_ty genv ctx.env ty)
          | None ->
              raise (Elab_error (Format.sprintf "Unbound variable: %s" name))))
  | App (f, a) -> (
      let f', f_ty = infer_tm genv ctx f in
      match f_ty with
      | VTyPi (_, a_ty, ClosTy (env, b_ty)) ->
          let a' = check_tm genv ctx a a_ty in
          let a_val = Nbe.eval_tm genv ctx.env a' in
          (TmApp (f', a'), Nbe.eval_ty genv (a_val :: env) b_ty)
      | _ -> raise (Elab_error "Expected function type in application"))
  | U -> raise (Elab_error "Cannot infer type of Type")
  | Ann (e, ty) ->
      let ty = check_ty genv ctx ty in
      let ty_val = Nbe.eval_ty genv ctx.env ty in
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
            let ty_val = Nbe.eval_ty genv ctx.env ty' in
            let ctx' = Context.bind name ty_val ctx in
            let body', body_ty = go ctx' rest in
            let clos = ClosTy (ctx.env, Quote.quote_ty genv ctx'.lvl body_ty) in
            (TmLam (name, ty', body'), VTyPi (name, ty_val, clos))
        | (_, None) :: _ ->
            raise (Elab_error "Cannot infer type of unannotated lambda :(")
      in
      go ctx (flatten_binders binders)
  | Pi ((names, dom), cod) ->
      let dom, _ = infer_tm genv ctx dom in
      let dom_val = Nbe.do_el (Nbe.eval_tm genv ctx.env dom) in
      let dom_tm_at (n : int) : tm =
        Quote.reify_ty genv (ctx.lvl + n) dom_val
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
      let dom_val = Nbe.do_el (Nbe.eval_tm genv ctx.env dom) in
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
      let a_code = Quote.reify_ty genv ctx.lvl a_ty in
      let b_code = Quote.reify_ty genv ctx.lvl b_ty in
      let prod_code = TmApp (TmApp (TmConst [ "Prod" ], a_code), b_code) in
      let pair_tm =
        TmApp
          ( TmApp (TmApp (TmApp (TmConst [ "Prod"; "mk" ], a_code), b_code), a),
            b )
      in
      let pair_ty = Nbe.eval_ty genv ctx.env (TyEl prod_code) in
      (pair_tm, pair_ty)
  | NatLit n -> infer_tm genv ctx (Desugar.desugar_nat_lit n)
  | Add (a, b) -> infer_tm genv ctx (Desugar.desugar_add a b)
  | Sub (a, b) -> infer_tm genv ctx (Desugar.desugar_sub a b)
  | Eq (a, b) ->
      let a_tm, a_ty = infer_tm genv ctx a in
      let b_tm, _ = infer_tm genv ctx b in
      let a_ty_tm = Quote.reify_ty genv ctx.lvl a_ty in
      (TmApp (TmApp (TmApp (TmConst [ "Eq" ], a_ty_tm), a_tm), b_tm), VTyU)
  | Let (name, ty_opt, rhs, body) ->
      let rhs', rhs_ty =
        match ty_opt with
        | Some ty ->
            let ty' = check_ty genv ctx ty in
            let ty_val = Nbe.eval_ty genv ctx.env ty' in
            (check_tm genv ctx rhs ty_val, ty_val)
        | None -> infer_tm genv ctx rhs
      in
      let rhs_val = Nbe.eval_tm genv ctx.env rhs' in
      let ctx' = Context.bind_def (Some name) rhs_ty rhs_val ctx in
      let body', body_ty = infer_tm genv ctx' body in
      let body_ty_quoted = Quote.quote_ty genv ctx'.lvl body_ty in
      let result_ty = Nbe.eval_ty genv ctx'.env body_ty_quoted in
      (TmLet (name, Quote.quote_ty genv ctx.lvl rhs_ty, rhs', body'), result_ty)
  | Sorry ->
      let id = fresh_sorry_id () in
      let hole_ty = VTyEl (HConst [ Format.sprintf "?ty%d†" id ], []) in
      (TmSorry (id, Quote.quote_ty genv ctx.lvl hole_ty), hole_ty)

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
                    let ann_val = Nbe.eval_ty genv ctx.env ann' in
                    if not (Nbe.conv_ty genv ctx.lvl ann_val a_ty) then
                      raise
                        (Elab_error
                           (Format.asprintf
                              "Lambda annotation mismatch: expected %a, got %a"
                              (Pretty.pp_ty_ctx (Context.names ctx))
                              (Quote.quote_ty genv ctx.lvl a_ty)
                              (Pretty.pp_ty_ctx (Context.names ctx))
                              (Quote.quote_ty genv ctx.lvl ann_val)))
                | None -> ());
                let ctx' = Context.bind name a_ty ctx in
                let var = VTmNeutral (HVar (Lvl ctx.lvl), []) in
                let b_ty_val = Nbe.eval_ty genv (var :: env) b_ty in
                let body' = go ctx' b_ty_val rest in
                TmLam (name, Quote.quote_ty genv ctx.lvl a_ty, body')
            | _ -> raise (Elab_error "Expected function type for lambda"))
      in
      go ctx expected (flatten_binders binders)
  | Pair (a, b), VTyEl (HConst [ "Sigma" ], [ a_code_val; b_val ]) ->
      let fst_ty = Nbe.do_el a_code_val in
      let a' = check_tm genv ctx a fst_ty in
      let a_val = Nbe.eval_tm genv ctx.env a' in
      let b_code_val = Nbe.do_app genv b_val a_val in
      let snd_ty = Nbe.do_el b_code_val in
      let b' = check_tm genv ctx b snd_ty in
      let a_code_tm = Quote.quote_tm genv ctx.lvl a_code_val in
      let b_tm = Quote.quote_tm genv ctx.lvl b_val in
      TmApp
        ( TmApp (TmApp (TmApp (TmConst [ "Sigma"; "mk" ], a_code_tm), b_tm), a'),
          b' )
  | Pair (a, b), VTyEl (HConst [ "Prod" ], [ a_code_val; b_val ]) ->
      let fst_ty = Nbe.do_el a_code_val in
      let snd_ty = Nbe.do_el b_val in
      let a' = check_tm genv ctx a fst_ty in
      let b' = check_tm genv ctx b snd_ty in
      let a_code_tm = Quote.quote_tm genv ctx.lvl a_code_val in
      let b_code_tm = Quote.quote_tm genv ctx.lvl b_val in
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
            let ty_val = Nbe.eval_ty genv ctx.env ty' in
            (check_tm genv ctx rhs ty_val, ty_val)
        | None -> infer_tm genv ctx rhs
      in
      let rhs_val = Nbe.eval_tm genv ctx.env rhs' in
      let ctx' = Context.bind_def (Some name) rhs_ty rhs_val ctx in
      let body' = check_tm genv ctx' body expected in
      TmLet (name, Quote.quote_ty genv ctx.lvl rhs_ty, rhs', body')
  | Sorry, expected ->
      let id = fresh_sorry_id () in
      TmSorry (id, Quote.quote_ty genv ctx.lvl expected)
  | _ ->
      let tm, inferred = infer_tm genv ctx raw in
      (if not (Nbe.conv_ty genv ctx.lvl inferred expected) then
         let names = Context.names ctx in
         raise
           (Elab_error
              (Format.asprintf "Type mismatch: expected %a, got %a"
                 (Pretty.pp_ty_ctx names)
                 (Quote.quote_ty genv ctx.lvl expected)
                 (Pretty.pp_ty_ctx names)
                 (Quote.quote_ty genv ctx.lvl inferred))));
      tm
