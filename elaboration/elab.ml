open Syntax

type name_ctx = string list

exception Elab_error of string

let lookup_var (names : name_ctx) (name : string) : int =
  match List.find_index (String.equal name) names with
  | Some ix -> ix
  | None -> raise (Elab_error ("Variable not in scope: " ^ name))

let fresh_meta_ctx (ctx : Check.context) : tm =
  let m = fresh_meta () in
  InsertedMeta (m, ctx.bds)

let unify_catch (ctx : Check.context) (t : val_ty) (u : val_ty) : unit =
  try Unify.unify ctx.lvl t u with
  | Unify.Unify_error ->
      let t_str = Quote.quote ctx.lvl t in
      let u_str = Quote.quote ctx.lvl u in
      raise
        (Elab_error
           (Format.asprintf "Cannot unify %a with %a" Pretty.pp_tm t_str
              Pretty.pp_tm u_str))

let rec check (ctx : Check.context) (names : name_ctx) (raw : Lang.Raw_syntax.t)
    (expected : val_ty) : tm =
  match (raw, Eval.force expected) with
  (* λx. body : Π x : A. B *)
  | Lambda (x, _, body), VPi (_, a, Closure (_, b)) ->
      let ctx' = Check.bind_var ctx a in
      let names' = x :: names in
      let b_val = Eval.eval (VRigid (ctx.lvl, []) :: ctx.env) b in
      let body' = check ctx' names' body b_val in
      Lam (x, body')
  (* let x : A = t in u *)
  | Let (x, ty_opt, t, u), expected -> (
      match ty_opt with
      | Some ty_raw ->
          let ty = check ctx names ty_raw VU in
          let val_ty = Eval.eval ctx.env ty in
          let t' = check ctx names t val_ty in
          let t_val = Eval.eval ctx.env t' in
          let u' =
            check (Check.bind_def ctx t_val val_ty) (x :: names) u expected
          in
          Let (x, ty, t', u')
      | None ->
          let t', val_ty = infer ctx names t in
          let t_val = Eval.eval ctx.env t' in
          let u' =
            check (Check.bind_def ctx t_val val_ty) (x :: names) u expected
          in
          (* Infer type for let binding *)
          Let (x, Quote.quote ctx.lvl val_ty, t', u'))
  (* Hole in checking mode *)
  | Hole, _ -> fresh_meta_ctx ctx
  (* Fallback: infer and unify *)
  | _, expected ->
      let t', inferred = infer ctx names raw in
      unify_catch ctx expected inferred;
      t'

(* Infer type for raw term *)
and infer (ctx : Check.context) (names : name_ctx) :
    Lang.Raw_syntax.t -> tm * val_ty = function
  (* Variable *)
  | Ident x ->
      let ix = lookup_var names x in
      let ty = List.nth ctx.types ix in
      (Var ix, ty)
  (* Lambda - insert meta for domain type if unannotated *)
  | Lambda (x, ty_opt, body) -> (
      match ty_opt with
      | Some ty_raw ->
          (* Annotated lambda *)
          let ty = check ctx names ty_raw VU in
          let val_ty = Eval.eval ctx.env ty in
          let ctx' = Check.bind_var ctx val_ty in
          let body', body_ty = infer ctx' (x :: names) body in
          ( Lam (x, body'),
            VPi (x, val_ty, Closure (ctx.env, Quote.quote (ctx.lvl + 1) body_ty))
          )
      | None ->
          (* Unannotated lambda - insert meta for domain type *)
          let val_ty = Eval.eval ctx.env (fresh_meta_ctx ctx) in
          let ctx' = Check.bind_var ctx val_ty in
          let body', body_ty = infer ctx' (x :: names) body in
          ( Lam (x, body'),
            VPi (x, val_ty, Closure (ctx.env, Quote.quote (ctx.lvl + 1) body_ty))
          ))
  (* Application *)
  | App (f, a) ->
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
  | Pi (x, a, b) ->
      let a' = check ctx names a VU in
      let a_val = Eval.eval ctx.env a' in
      let b' = check (Check.bind_var ctx a_val) (x :: names) b VU in
      (Pi (x, a', b'), VU)
  (* Arrow type, desugar to Pi type *)
  | Arrow (a, b) ->
      let a' = check ctx names a VU in
      let a_val = Eval.eval ctx.env a' in
      let b' = check (Check.bind_var ctx a_val) ("_" :: names) b VU in
      (Pi ("_", a', b'), VU)
  (* Let *)
  | Let (x, ty_opt, t, u) -> (
      match ty_opt with
      | Some ty_raw ->
          let ty = check ctx names ty_raw VU in
          let val_ty = Eval.eval ctx.env ty in
          let t' = check ctx names t val_ty in
          let t_val = Eval.eval ctx.env t' in
          let u', u_ty =
            infer (Check.bind_def ctx t_val val_ty) (x :: names) u
          in
          (Let (x, ty, t', u'), u_ty)
      | None ->
          let t', val_ty = infer ctx names t in
          let t_val = Eval.eval ctx.env t' in
          let u', u_ty =
            infer (Check.bind_def ctx t_val val_ty) (x :: names) u
          in
          (Let (x, Quote.quote ctx.lvl val_ty, t', u'), u_ty))
  (* Universe *)
  | U -> (U, VU)
  (* Unit type *)
  | Unit -> (Unit, VU)
  (* Unit term *)
  | UnitTerm -> (UnitTerm, VUnit)
  (* Hole in inference mode - create meta for both term and type *)
  | Hole ->
      let val_ty = Eval.eval ctx.env (fresh_meta_ctx ctx) in
      let tm = fresh_meta_ctx ctx in
      (tm, val_ty)

let elab_def (ctx : Check.context) (names : name_ctx)
    ((name, ty_opt, body) : Lang.Raw_syntax.def) :
    string * tm * val_ty * Check.context * name_ctx =
  let body', body_ty =
    match ty_opt with
    | Some ty_raw ->
        let ty = check ctx names ty_raw VU in
        let val_ty = Eval.eval ctx.env ty in
        let body' = check ctx names body val_ty in
        (body', val_ty)
    | None -> infer ctx names body
  in
  let body_val = Eval.eval ctx.env body' in
  let ctx' = Check.bind_def ctx body_val body_ty in
  let names' = name :: names in
  (name, body', body_ty, ctx', names')

let elab_program (program : Lang.Raw_syntax.program) :
    (string * tm * val_ty) list =
  let rec go ctx names defs acc =
    match defs with
    | [] -> List.rev acc
    | def :: rest ->
        let name, term, ty, ctx', names' = elab_def ctx names def in
        go ctx' names' rest ((name, term, ty) :: acc)
  in
  go Check.empty_context [] program []
