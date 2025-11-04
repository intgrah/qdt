open Syntax
open Eval

exception Unify_error

module IntMap = Map.Make (Int)

type partial_renaming = {
  dom : lvl; (* size of domain context *)
  cod : lvl; (* size of codomain context *)
  ren : lvl IntMap.t; (* domain variables => codomain variables *)
}

let lift (pren : partial_renaming) : partial_renaming =
  {
    dom = pren.dom + 1;
    cod = pren.cod + 1;
    ren = IntMap.add pren.cod pren.dom pren.ren;
  }

let ix_of_lvl (l : lvl) (x : lvl) : ix = l - x - 1

let invert (gamma : lvl) (sp : spine) : partial_renaming =
  let rec go (sp : spine) (dom : lvl) (ren : lvl IntMap.t) : lvl * lvl IntMap.t
      =
    match sp with
    | [] -> (dom, ren)
    | FApp (v, _ty) :: rest -> (
        let dom', ren' = go rest dom ren in
        match force (TmVal v) with
        | TmVal (VNeutral { head = HVar x; spine = []; boundary = _ }) ->
            if IntMap.mem x ren' then raise Unify_error
            else (dom' + 1, IntMap.add x dom' ren')
        | _ -> raise Unify_error)
  in
  let dom, ren = go (List.rev sp) 0 IntMap.empty in
  { dom; cod = gamma; ren }

(* Rename rhs using partial renaming, with occurs check for m *)
let rec rename (m : meta_id) (pren : partial_renaming) (v : tm_val) : tm =
  let rec go_sp (t : tm) : spine -> tm = function
    | [] -> t
    | FApp (u, _ty) :: rest ->
        let t' = go_sp t rest in
        App (t', rename m pren u)
  in

  match force (TmVal v) with
  | TmVal (VNeutral { head = HMeta m'; spine; boundary = _ }) ->
      if m = m' then raise Unify_error (* occurs check *)
      else go_sp (Meta m') spine
  | TmVal (VNeutral { head = HVar x; spine; boundary = _ }) -> (
      match IntMap.find_opt x pren.ren with
      | None -> raise Unify_error (* out of scope *)
      | Some x' -> go_sp (Var (ix_of_lvl pren.dom x')) spine)
  | TmVal (VLam (Closure_tm (env, body))) ->
      let pren' = lift pren in
      let body_val =
        eval_tm
          (TmVal
             (VNeutral
                {
                  head = HVar pren.cod;
                  spine = [];
                  boundary = lazy (Abstract VType);
                })
          :: env)
          body
      in
      Lam (Type, rename m pren' body_val)
  | _ -> raise Unify_error

(* Wrap term in n lambdas *)
let rec lams (n : lvl) (t : tm) : tm =
  if n = 0 then t else Lam (Type, lams (n - 1) t)

(* ?m spine = rhs *)
let solve (gamma : lvl) (m : meta_id) (sp : spine) (rhs : tm_val) : unit =
  let pren = invert gamma sp in
  let rhs_tm = rename m pren rhs in
  let solution = eval_tm [] (lams pren.dom rhs_tm) in
  solve_meta m solution

let rec unify_ty (l : lvl) (t : ty_val) (u : ty_val) : unit =
  match (t, u) with
  | VPi (a1, Closure_ty (env1, b1)), VPi (a2, Closure_ty (env2, b2)) ->
      unify_ty l a1 a2;
      let x_var : tm_val =
        VNeutral { head = HVar l; spine = []; boundary = lazy (Abstract a1) }
      in
      let b1_val = Eval.eval_ty (TmVal x_var :: env1) b1 in
      let b2_val = Eval.eval_ty (TmVal x_var :: env2) b2 in
      unify_ty (l + 1) b1_val b2_val
  | VType, VType -> ()
  | ( VNeutral { head = HVar x1; spine = sp1; boundary = _ },
      VNeutral { head = HVar x2; spine = sp2; boundary = _ } ) ->
      if x1 = x2 then unify_sp l sp1 sp2 else raise Unify_error
  | _ -> raise Unify_error

and unify_sp (l : lvl) (sp1 : spine) (sp2 : spine) : unit =
  match (sp1, sp2) with
  | [], [] -> ()
  | FApp (t1, _) :: rest1, FApp (t2, _) :: rest2 ->
      unify_sp l rest1 rest2;
      unify l t1 t2
  | _ -> raise Unify_error

and unify (l : lvl) (t : tm_val) (u : tm_val) : unit =
  let t =
    match force (TmVal t) with
    | TmVal x -> x
    | _ -> failwith "unify: force got ty_val"
  in
  let u =
    match force (TmVal u) with
    | TmVal x -> x
    | _ -> failwith "unify: force got ty_val"
  in
  match (t, u) with
  (* Pattern unification *)
  | VNeutral { head = HMeta m; spine; boundary = _ }, u -> solve l m spine u
  | t, VNeutral { head = HMeta m; spine; boundary = _ } -> solve l m spine t
  (* eta expansion *)
  | VLam (Closure_tm (env1, body1)), VLam (Closure_tm (env2, body2)) ->
      let v : tm_val =
        VNeutral { head = HVar l; spine = []; boundary = lazy (Abstract VType) }
      in
      unify (l + 1)
        (eval_tm (TmVal v :: env1) body1)
        (eval_tm (TmVal v :: env2) body2)
  | VLam (Closure_tm (env, body)), u ->
      let v : tm_val =
        VNeutral { head = HVar l; spine = []; boundary = lazy (Abstract VType) }
      in
      let t_app = eval_tm (TmVal v :: env) body in
      let u_app =
        match apply (TmVal u) (TmVal v) with
        | TmVal x -> x
        | _ -> failwith "unify: apply got ty_val"
      in
      unify (l + 1) t_app u_app
  | t, VLam (Closure_tm (env, body)) ->
      let v : tm_val =
        VNeutral { head = HVar l; spine = []; boundary = lazy (Abstract VType) }
      in
      let t_app =
        match apply (TmVal t) (TmVal v) with
        | TmVal x -> x
        | _ -> failwith "unify: apply got ty_val"
      in
      let u_app = eval_tm (TmVal v :: env) body in
      unify (l + 1) t_app u_app
  | ( VNeutral { head = HVar x1; spine = sp1; boundary = _ },
      VNeutral { head = HVar x2; spine = sp2; boundary = _ } ) ->
      if x1 = x2 then unify_sp l sp1 sp2 else raise Unify_error
