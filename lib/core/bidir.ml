open Syntax
open Semantics
open Frontend

let fresh_sorry_id =
  let counter = ref 0 in
  fun () ->
    let id = !counter in
    incr counter;
    id

let rec check_ty (genv : Global.t) (ctx : Context.t) : Ast.t -> ty = function
  | Missing src -> Error.raise ~kind:Type_check "Missing term" src
  | U _ -> TyU
  | Pi (_src, (_, name, dom), cod) ->
      let dom = check_ty genv ctx dom in
      let dom_val = Nbe.eval_ty genv ctx.env dom in
      let ctx' = Context.bind name dom_val ctx in
      let cod = check_ty genv ctx' cod in
      TyPi (name, dom, cod)
  | Eq (_src, a, b) ->
      let a_tm, a_ty = infer_tm genv ctx a in
      let b_tm, _ = infer_tm genv ctx b in
      let a_ty_tm = Quote.reify_ty genv ctx.lvl a_ty in
      let eq_ty =
        TyEl (TmApp (TmApp (TmApp (TmConst [ "Eq" ], a_ty_tm), a_tm), b_tm))
      in
      eq_ty
  | t ->
      let tm, ty_val = infer_tm genv ctx t in
      if not (Nbe.conv_ty genv ctx.lvl ty_val Semantics.VTyU) then
        Error.raise ~kind:Type_check
          (Format.asprintf "Expected Type, got %a"
             (Pretty.pp_ty_ctx (Context.names ctx))
             (Quote.quote_ty genv ctx.lvl ty_val))
          (Ast.get_src t);
      TyEl tm

and infer_tm (genv : Global.t) (ctx : Context.t) : Ast.t -> tm * vty = function
  | Missing src -> Error.raise ~kind:Type_check "Missing term" src
  | Ident (src, name) -> (
      match Context.lookup_name ctx name with
      | Some (k, ty) -> (TmVar (Idx k), ty)
      | None -> (
          let fqn = Name.parse name in
          match Global.find_ty fqn genv with
          | Some ty -> (TmConst fqn, Nbe.eval_ty genv ctx.env ty)
          | None ->
              Error.raise ~kind:Type_check
                (Format.sprintf "Unbound variable: %s" name)
                src))
  | App (src, f, a) -> (
      let f', f_ty = infer_tm genv ctx f in
      match f_ty with
      | Semantics.VTyPi (_, a_ty, Semantics.ClosTy (env, b_ty)) ->
          let a' = check_tm genv ctx a a_ty in
          let a_val = Nbe.eval_tm genv ctx.env a' in
          (TmApp (f', a'), Nbe.eval_ty genv (a_val :: env) b_ty)
      | _ ->
          Error.raise ~kind:Type_check "Expected function type in application"
            src)
  | U src -> Error.raise ~kind:Type_check "Cannot infer type of Type" src
  | Ann (_src, e, ty) ->
      let ty = check_ty genv ctx ty in
      let ty_val = Nbe.eval_ty genv ctx.env ty in
      let e = check_tm genv ctx e ty_val in
      (e, ty_val)
  | Lam (src, binder, body) -> (
      match binder with
      | Ast.Untyped _ ->
          Error.raise ~kind:Type_check
            "Cannot infer type of unannotated lambda :(" src
      | Ast.Typed (_, name_opt, ty) ->
          let ty' = check_ty genv ctx ty in
          let ty_val = Nbe.eval_ty genv ctx.env ty' in
          let ctx' = Context.bind name_opt ty_val ctx in
          let body', body_ty = infer_tm genv ctx' body in
          let clos =
            Semantics.ClosTy (ctx.env, Quote.quote_ty genv ctx'.lvl body_ty)
          in
          ( TmLam (name_opt, ty', body'),
            Semantics.VTyPi (name_opt, ty_val, clos) ))
  | Pi (_src, (_, name_opt, dom), cod) ->
      let dom, _ = infer_tm genv ctx dom in
      let dom_val = Nbe.do_el (Nbe.eval_tm genv ctx.env dom) in
      let ctx' = Context.bind name_opt dom_val ctx in
      let cod_tm, _ = infer_tm genv ctx' cod in
      (TmPiHat (name_opt, dom, cod_tm), VTyU)
  | Pair (_src, a, b) ->
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
  | Eq (_src, a, b) ->
      let a_tm, a_ty = infer_tm genv ctx a in
      let b_tm, _ = infer_tm genv ctx b in
      let a_ty_tm = Quote.reify_ty genv ctx.lvl a_ty in
      ( TmApp (TmApp (TmApp (TmConst [ "Eq" ], a_ty_tm), a_tm), b_tm),
        Semantics.VTyU )
  | Let (_src, name, ty_opt, rhs, body) ->
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
  | Sorry src -> Error.raise ~kind:Type_check "Cannot infer type of sorry" src

and check_tm (genv : Global.t) (ctx : Context.t) (raw : Ast.t) (expected : vty)
    : tm =
  match (raw, expected) with
  | ( Lam (_src, binder, body),
      Semantics.VTyPi (_, a_ty, Semantics.ClosTy (env, b_ty)) ) -> (
      match binder with
      | Ast.Untyped (_, name) ->
          let ctx' = Context.bind name a_ty ctx in
          let var =
            Semantics.VTmNeutral (Semantics.HVar (Semantics.Lvl.Lvl ctx.lvl), [])
          in
          let b_ty_val = Nbe.eval_ty genv (var :: env) b_ty in
          let body' = check_tm genv ctx' body b_ty_val in
          TmLam (name, Quote.quote_ty genv ctx.lvl a_ty, body')
      | Ast.Typed (binder_src, name_opt, ann) ->
          let ann' = check_ty genv ctx ann in
          let ann_val = Nbe.eval_ty genv ctx.env ann' in
          if not (Nbe.conv_ty genv ctx.lvl ann_val a_ty) then
            Error.raise ~kind:Type_check
              (Format.asprintf "Lambda annotation mismatch: expected %a, got %a"
                 (Pretty.pp_ty_ctx (Context.names ctx))
                 (Quote.quote_ty genv ctx.lvl a_ty)
                 (Pretty.pp_ty_ctx (Context.names ctx))
                 (Quote.quote_ty genv ctx.lvl ann_val))
              binder_src;
          let ctx' = Context.bind name_opt a_ty ctx in
          let var =
            Semantics.VTmNeutral (Semantics.HVar (Semantics.Lvl.Lvl ctx.lvl), [])
          in
          let b_ty_val = Nbe.eval_ty genv (var :: env) b_ty in
          let body' = check_tm genv ctx' body b_ty_val in
          TmLam (name_opt, Quote.quote_ty genv ctx.lvl a_ty, body'))
  | Lam (src, _, _), _ ->
      Error.raise ~kind:Type_check "Expected function type for lambda" src
  | ( Pair (_src, a, b),
      Semantics.VTyEl (Semantics.HConst [ "Prod" ], [ a_code_val; b_val ]) ) ->
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
  | Pair (src, _, _), Semantics.VTyEl (Semantics.HConst [ _ ], [ _; _ ]) ->
      Error.raise ~kind:Type_check "Expected product type in pair" src
  | Let (_src, name, ty_opt, rhs, body), expected ->
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
  | Sorry _src, expected ->
      let id = fresh_sorry_id () in
      TmSorry (id, Quote.quote_ty genv ctx.lvl expected)
  | raw, expected ->
      let tm, inferred = infer_tm genv ctx raw in
      (if not (Nbe.conv_ty genv ctx.lvl inferred expected) then
         let names = Context.names ctx in
         Error.raise ~kind:Type_check
           (Format.asprintf "Type mismatch: expected %a, got %a"
              (Pretty.pp_ty_ctx names)
              (Quote.quote_ty genv ctx.lvl expected)
              (Pretty.pp_ty_ctx names)
              (Quote.quote_ty genv ctx.lvl inferred))
           (Ast.get_src raw));
      tm
