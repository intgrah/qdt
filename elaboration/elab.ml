open Syntax

type name_ctx = string list

exception Elab_error of string

let lookup_var (names : name_ctx) (name : string) : int option =
  List.find_index (String.equal name) names

let fresh_meta_ctx (ctx : Check.context) : tm =
  let m = fresh_meta () in
  InsertedMeta (m, ctx.bds)

let unify_catch (ctx : Check.context) (t : vl) (u : vl) : unit =
  try Unify.unify ctx.lvl t u with
  | Unify.Unify_error ->
      let t_str = Quote.quote ctx.lvl t in
      let u_str = Quote.quote ctx.lvl u in
      raise
        (Elab_error
           (Format.asprintf "Cannot unify %a with %a" Pretty.pp_tm t_str
              Pretty.pp_tm u_str))

let rec check (ctx : Check.context) (names : name_ctx) (raw : Lang.Raw_syntax.t)
    (expected : vl) : tm =
  match (raw, Eval.force expected) with
  (* λx => body : Π x : A. B *)
  | RLambda (x, _, body), VPi (_, a, Closure (_, b)) ->
      let ctx' = Check.bind_var ctx a in
      let names' = x :: names in
      let b_val = Eval.eval (VRigid (ctx.lvl, []) :: ctx.env) b in
      let body' = check ctx' names' body b_val in
      Lam (x, body')
  (* let x : A = t in u *)
  | RLet (x, ty_opt, t, u), expected -> (
      match ty_opt with
      | Some ty_raw ->
          let ty = check ctx names ty_raw VU in
          let vl = Eval.eval ctx.env ty in
          let t' = check ctx names t vl in
          let t_val = Eval.eval ctx.env t' in
          let u' =
            check (Check.bind_def ctx t_val vl) (x :: names) u expected
          in
          Let (x, ty, t', u')
      | None ->
          let t', vl = infer ctx names t in
          let t_val = Eval.eval ctx.env t' in
          let u' =
            check (Check.bind_def ctx t_val vl) (x :: names) u expected
          in
          (* Infer type for let binding *)
          Let (x, Quote.quote ctx.lvl vl, t', u'))
  (* Pair in checking mode *)
  | RPair (a, b), VProd (a_ty, b_ty) ->
      let a' = check ctx names a a_ty in
      let b' = check ctx names b b_ty in
      Pair (a', b')
  (* Hole in checking mode *)
  | RHole, _ -> fresh_meta_ctx ctx
  (* Fallback: infer and unify *)
  | _, expected ->
      let t', inferred = infer ctx names raw in
      unify_catch ctx expected inferred;
      t'

(* Infer type of raw term *)
and infer (ctx : Check.context) (names : name_ctx) :
    Lang.Raw_syntax.t -> tm * vl = function
  (* Variable or Global *)
  | RIdent x -> (
      match lookup_var names x with
      | Some ix ->
          (* Local variable *)
          let ty = List.nth ctx.types ix in
          (Var ix, ty)
      | None -> (
          match lookup_global x with
          | Some entry -> (Global x, entry.ty)
          | None -> raise (Elab_error ("Variable not in scope: " ^ x))))
  (* Lambda - insert meta for domain type if unannotated *)
  | RLambda (x, ty_opt, body) -> (
      match ty_opt with
      | Some ty_raw ->
          (* Annotated lambda *)
          let ty = check ctx names ty_raw VU in
          let vl = Eval.eval ctx.env ty in
          let ctx' = Check.bind_var ctx vl in
          let body', body_ty = infer ctx' (x :: names) body in
          ( Lam (x, body'),
            VPi (x, vl, Closure (ctx.env, Quote.quote (ctx.lvl + 1) body_ty)) )
      | None ->
          (* Unannotated lambda - insert meta for domain type *)
          let vl = Eval.eval ctx.env (fresh_meta_ctx ctx) in
          let ctx' = Check.bind_var ctx vl in
          let body', body_ty = infer ctx' (x :: names) body in
          ( Lam (x, body'),
            VPi (x, vl, Closure (ctx.env, Quote.quote (ctx.lvl + 1) body_ty)) ))
  (* Application *)
  | RApp (f, a) ->
      let f', f_ty = infer ctx names f in
      (* Ensure f_ty is a Pi type, inserting metas if needed *)
      let a_ty, b_clos =
        match Eval.force f_ty with
        | VPi (_, a, b) -> (a, b)
        | _ -> (
            (* Not a Pi - insert metas and unify *)
            let a_val = Eval.eval ctx.env (fresh_meta_ctx ctx) in
            let b_tm = fresh_meta_ctx (Check.bind_var ctx a_val) in
            let pi_ty = VPi ("_", a_val, Closure (ctx.env, b_tm)) in
            unify_catch ctx pi_ty f_ty;
            match Eval.force pi_ty with
            | VPi (_, a, b) -> (a, b)
            | _ -> failwith "impossible")
      in
      let a' = check ctx names a a_ty in
      let a_val = Eval.eval ctx.env a' in
      let (Closure (env, b)) = b_clos in
      let b_val = Eval.eval (a_val :: env) b in
      (App (f', a'), b_val)
  (* Pi type *)
  | RPi (x, a, b) ->
      let a' = check ctx names a VU in
      let a_val = Eval.eval ctx.env a' in
      let b' = check (Check.bind_var ctx a_val) (x :: names) b VU in
      (Pi (x, a', b'), VU)
  (* Arrow type, desugar to Pi type *)
  | RArrow (a, b) ->
      let a' = check ctx names a VU in
      let a_val = Eval.eval ctx.env a' in
      let b' = check (Check.bind_var ctx a_val) ("_" :: names) b VU in
      (Pi ("_", a', b'), VU)
  (* Let *)
  | RLet (x, ty_opt, t, u) -> (
      match ty_opt with
      | Some ty_raw ->
          let ty = check ctx names ty_raw VU in
          let vl = Eval.eval ctx.env ty in
          let t' = check ctx names t vl in
          let t_val = Eval.eval ctx.env t' in
          let u', u_ty = infer (Check.bind_def ctx t_val vl) (x :: names) u in
          (Let (x, ty, t', u'), u_ty)
      | None ->
          let t', vl = infer ctx names t in
          let t_val = Eval.eval ctx.env t' in
          let u', u_ty = infer (Check.bind_def ctx t_val vl) (x :: names) u in
          (Let (x, Quote.quote ctx.lvl vl, t', u'), u_ty))
  (* Universe *)
  | RU -> (U, VU)
  (* Unit type *)
  | RUnit -> (Unit, VU)
  (* Unit term *)
  | RUnitTerm -> (UnitTerm, VUnit)
  (* Product type *)
  | RProd (a, b) ->
      let a' = check ctx names a VU in
      let b' = check ctx names b VU in
      (Prod (a', b'), VU)
  (* Pair *)
  | RPair (a, b) ->
      let a', a_ty = infer ctx names a in
      let b', b_ty = infer ctx names b in
      (Pair (a', b'), VProd (a_ty, b_ty))
  (* First projection *)
  | RFst t -> (
      let t', t_ty = infer ctx names t in
      match Eval.force t_ty with
      | VProd (a, _) -> (Fst t', a)
      | _ ->
          let a_val = Eval.eval ctx.env (fresh_meta_ctx ctx) in
          let b_val = Eval.eval ctx.env (fresh_meta_ctx ctx) in
          let prod_ty = VProd (a_val, b_val) in
          unify_catch ctx prod_ty t_ty;
          (Fst t', a_val))
  (* Second projection *)
  | RSnd t -> (
      let t', t_ty = infer ctx names t in
      match Eval.force t_ty with
      | VProd (_, b) -> (Snd t', b)
      | _ ->
          let a_val = Eval.eval ctx.env (fresh_meta_ctx ctx) in
          let b_val = Eval.eval ctx.env (fresh_meta_ctx ctx) in
          let prod_ty = VProd (a_val, b_val) in
          unify_catch ctx prod_ty t_ty;
          (Snd t', b_val))
  (* Hole in inference mode - create meta for both term and type *)
  | RHole ->
      let vl = Eval.eval ctx.env (fresh_meta_ctx ctx) in
      let tm = fresh_meta_ctx ctx in
      (tm, vl)

let elab_def (ctx : Check.context) (names : name_ctx)
    ((name, ty_opt, body) : Lang.Raw_syntax.def) : string * tm * vl =
  let body', body_ty =
    match ty_opt with
    | Some ty_raw ->
        let ty = check ctx names ty_raw VU in
        let vl = Eval.eval ctx.env ty in
        let body' = check ctx names body vl in
        (body', vl)
    | None -> infer ctx names body
  in
  let body_val = Eval.eval ctx.env body' in
  (* Add to global table instead of context *)
  define_global name body_val body_ty;
  (name, body', body_ty)

let elab_program (program : Lang.Raw_syntax.program) : (string * tm * vl) list =
  let rec go defs acc =
    match defs with
    | [] -> List.rev acc
    | def :: rest ->
        let name, term, ty = elab_def Check.empty_context [] def in
        go rest ((name, term, ty) :: acc)
  in
  (* Reset global table before elaborating *)
  reset_global_context ();
  go program []
