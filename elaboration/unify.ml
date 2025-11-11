open Syntax
open Eval

exception Unify_error

module IntMap = Map.Make (Int)

(* Partial renaming from Γ to Δ *)
type partial_renaming = {
  dom : lvl; (* size of Γ *)
  cod : lvl; (* size of Δ *)
  ren : lvl IntMap.t; (* mapping from Δ vars to Γ vars *)
}

(* Lift partial renaming over an extra bound variable *)
let lift (pren : partial_renaming) : partial_renaming =
  {
    dom = pren.dom + 1;
    cod = pren.cod + 1;
    ren = IntMap.add pren.cod pren.dom pren.ren;
  }

(* Invert spine to partial renaming *)
let invert_spine (gamma : lvl) (sp : spine) : partial_renaming =
  let rec go sp dom ren =
    match sp with
    | [] -> (dom, ren)
    | t :: rest -> (
        match force t with
        | VRigid (x, []) ->
            if IntMap.mem x ren then
              raise Unify_error
            else
              go rest (dom + 1) (IntMap.add x dom ren)
        | _ -> raise Unify_error)
  in
  let dom, ren = go sp 0 IntMap.empty in
  { dom; cod = gamma; ren }

(* Rename rhs using partial renaming, with occurs check for m *)
let rec rename (m : meta_id) (pren : partial_renaming) (v : val_ty) : tm =
  let rec goSp t sp =
    match sp with
    | [] -> t
    | u :: rest -> App (goSp t rest, rename m pren u)
  in

  match force v with
  | VFlex (m', sp) ->
      if m = m' then
        raise Unify_error
      (* occurs *)
      else
        goSp (Meta m') sp
  | VRigid (x, sp) -> (
      match IntMap.find_opt x pren.ren with
      | None -> raise Unify_error (* scope error *)
      | Some x' -> goSp (Var (Quote.ix_of_lvl pren.dom x')) sp)
  | VLam (x, Closure (env, body)) ->
      let pren' = lift pren in
      Lam (x, rename m pren' (eval (VRigid (pren.cod, []) :: env) body))
  | VPi (x, a, Closure (env, b)) ->
      let pren' = lift pren in
      Pi
        ( x,
          rename m pren a,
          rename m pren' (eval (VRigid (pren.cod, []) :: env) b) )
  | VU -> U

(* Wrap term in n lambdas *)
let lams (n : lvl) (t : tm) : tm =
  let rec go i t =
    if i = n then
      t
    else
      go (i + 1) (Lam ("x" ^ string_of_int i, t))
  in
  go 0 t

(* Solve ?m spine = rhs *)
let solve (gamma : lvl) (m : meta_id) (sp : spine) (rhs : val_ty) : unit =
  let pren = invert_spine gamma sp in
  let rhs_tm = rename m pren rhs in
  let solution = eval [] (lams pren.dom rhs_tm) in
  solve_meta m solution

(* Unify spines *)
let rec unify_spine (l : lvl) (sp1 : spine) (sp2 : spine) : unit =
  match (sp1, sp2) with
  | [], [] -> ()
  | t1 :: rest1, t2 :: rest2 ->
      unify_spine l rest1 rest2;
      unify l t1 t2
  | _ -> raise Unify_error

and unify (l : lvl) (t : val_ty) (u : val_ty) : unit =
  let appl_clos (Closure (env, body)) v = eval (v :: env) body in
  match (force t, force u) with
  (* Eta for lambdas *)
  | VLam (_, t), VLam (_, u) ->
      unify (l + 1)
        (appl_clos t (VRigid (l, [])))
        (appl_clos u (VRigid (l, [])))
  | VLam (_, t), u ->
      unify (l + 1) (appl_clos t (VRigid (l, []))) (apply_ty u (VRigid (l, [])))
  | t, VLam (_, u) ->
      unify (l + 1) (apply_ty t (VRigid (l, []))) (appl_clos u (VRigid (l, [])))
  (* Rigid cases *)
  | VU, VU -> ()
  | VPi (_, a, b), VPi (_, a', b') ->
      unify l a a';
      unify (l + 1)
        (appl_clos b (VRigid (l, [])))
        (appl_clos b' (VRigid (l, [])))
  | VRigid (x, sp), VRigid (x', sp') when x = x' -> unify_spine l sp sp'
  | VFlex (m, sp), VFlex (m', sp') when m = m' -> unify_spine l sp sp'
  (* Pattern unification *)
  | VFlex (m, sp), t -> solve l m sp t
  | t, VFlex (m, sp) -> solve l m sp t
  | _ -> raise Unify_error
