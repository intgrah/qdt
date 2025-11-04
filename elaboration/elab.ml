open Syntax

type name_ctx = string list

exception Elab_error of string
exception Unbound_variable of string

(* name => de Bruijn index *)
let lookup_var (name : string) (names : name_ctx) : int =
  match List.find_index (String.equal name) names with
  | None -> raise (Unbound_variable name)
  | Some ix -> ix

let rec elab_infer (ctx : Check.context) (names : name_ctx)
    (raw : Lang.Raw_syntax.t) : tm * ty_val =
  match raw with
  | Ident name ->
      let ix = lookup_var name names in
      let ty = List.nth ctx.types ix in
      (Var ix, ty)
  | Lambda (name, ann_opt, body) -> (
      match ann_opt with
      | Some ann_raw ->
          let ann_ty = elab_check_ty ctx names ann_raw in
          let ann_ty_val = Eval.eval_ty ctx.env ann_ty in
          let ctx' = Check.bind_var ctx ann_ty_val in
          let names' = name :: names in
          let body', body_ty = elab_infer ctx' names' body in
          let body_ty_quoted = Quote.quote_ty (ctx.lvl + 1) body_ty in
          ( Lam (ann_ty, body'),
            VPi (ann_ty_val, Closure_ty (ctx.env, body_ty_quoted)) )
      | None -> raise (Elab_error "Cannot infer type of unannotated lambda"))
  | App (f, a) -> (
      let f', f_ty = elab_infer ctx names f in
      match Eval.force (TyVal f_ty) with
      | TyVal (VPi (a_ty, Closure_ty (env, b_ty))) ->
          let a' = elab_check ctx names a a_ty in
          let a_val = Eval.eval_tm ctx.env a' in
          let b_val = Eval.eval_ty (TmVal a_val :: env) b_ty in
          (App (f', a'), b_val)
      | _ -> raise (Elab_error "Application of non-function type"))
  | Pi _ -> raise (Elab_error "Pi types cannot appear in term position")
  | Arrow _ -> raise (Elab_error "Arrow types cannot appear in term position")
  | Let (name, ty_opt, rhs, body) ->
      let rhs', rhs_ty =
        match ty_opt with
        | Some ty_raw ->
            let ty = elab_check_ty ctx names ty_raw in
            let ty_val = Eval.eval_ty ctx.env ty in
            let rhs' = elab_check ctx names rhs ty_val in
            (rhs', ty_val)
        | None -> elab_infer ctx names rhs
      in
      let _rhs_val = Eval.eval_tm ctx.env rhs' in
      let lam_body, body_ty =
        elab_infer (Check.bind_var ctx rhs_ty) (name :: names) body
      in
      let _body_ty_quoted = Quote.quote_ty (ctx.lvl + 1) body_ty in
      let lam_ty_quoted = Quote.quote_ty ctx.lvl rhs_ty in
      (App (Lam (lam_ty_quoted, lam_body), rhs'), body_ty)
  | Hole ->
      let m = fresh_meta () in
      (Meta m, VType)
  | Type -> raise (Elab_error "Type is not a term")

and elab_check (ctx : Check.context) (names : name_ctx)
    (raw : Lang.Raw_syntax.t) (expected : ty_val) : tm =
  match (raw, expected) with
  | Lambda (name, _ann_opt, body), VPi (a, Closure_ty (_, b_ty)) ->
      let ctx' = Check.bind_var ctx a in
      let names' = name :: names in
      let x_var : tm_val =
        VNeutral
          { head = HVar ctx.lvl; spine = []; boundary = lazy (Abstract a) }
      in
      let b_val = Eval.eval_ty (TmVal x_var :: ctx.env) b_ty in
      let body' = elab_check ctx' names' body b_val in
      let a_quoted = Quote.quote_ty ctx.lvl a in
      Lam (a_quoted, body')
  (* Switch to infer and unify *)
  | _ -> (
      let t', inferred = elab_infer ctx names raw in
      try
        Unify.unify_ty ctx.lvl inferred expected;
        t'
      with
      | Unify.Unify_error ->
          let inferred_str = Pretty.ty_val_to_string inferred in
          let expected_str = Pretty.ty_val_to_string expected in
          raise
            (Elab_error
               (Format.sprintf "Type mismatch: inferred %s but expected %s"
                  inferred_str expected_str)))

and elab_check_ty (ctx : Check.context) (names : name_ctx)
    (raw : Lang.Raw_syntax.t) : ty =
  match raw with
  | Ident name ->
      let ix = lookup_var name names in
      TVar ix
  | Pi (name, a, b) ->
      let a_ty = elab_check_ty ctx names a in
      let a_val = Eval.eval_ty ctx.env a_ty in
      let ctx' = Check.bind_var ctx a_val in
      let names' = name :: names in
      let b_ty = elab_check_ty ctx' names' b in
      Pi (a_ty, b_ty)
  | Arrow (a, b) ->
      let a_ty = elab_check_ty ctx names a in
      let a_val = Eval.eval_ty ctx.env a_ty in
      let ctx' = Check.bind_var ctx a_val in
      let names' = "_" :: names in
      let b_ty = elab_check_ty ctx' names' b in
      Pi (a_ty, b_ty)
  | Type -> Type
  | _ -> raise (Elab_error "Expected type")

let elab_def (ctx : Check.context) (names : name_ctx)
    ((name, ty_opt, body) : Lang.Raw_syntax.def) :
    tm * ty_val * Check.context * name_ctx =
  let body', body_ty =
    match ty_opt with
    | Some ty_raw ->
        let ty = elab_check_ty ctx names ty_raw in
        let ty_val = Eval.eval_ty ctx.env ty in
        let body' = elab_check ctx names body ty_val in
        (body', ty_val)
    | None -> elab_infer ctx names body
  in
  let body_val = Eval.eval_tm ctx.env body' in
  let ctx' =
    {
      Check.env = TmVal body_val :: ctx.env;
      lvl = ctx.lvl + 1;
      types = body_ty :: ctx.types;
    }
  in
  let names' = name :: names in
  (body', body_ty, ctx', names')

let elab_program (program : Lang.Raw_syntax.program) :
    (string * tm * ty_val) list =
  let rec go ctx names defs acc =
    match defs with
    | [] -> List.rev acc
    | def :: rest ->
        let name, _, _ = def in
        let term, ty, ctx', names' = elab_def ctx names def in
        go ctx' names' rest ((name, term, ty) :: acc)
  in
  go Check.empty_context [] program []
