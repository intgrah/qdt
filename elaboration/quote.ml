open Syntax

let ix_of_lvl (l : lvl) (x : lvl) : ix = l - x - 1

let rec quote_sp (l : lvl) (t : tm) (sp : spine) : tm =
  match sp with
  | [] -> t
  | FApp u :: sp' -> App (quote_sp l t sp', quote l u)
  | FFst :: sp' -> Fst (quote_sp l t sp')
  | FSnd :: sp' -> Snd (quote_sp l t sp')

and quote (l : lvl) (v : val_ty) : tm =
  match Eval.force v with
  | VFlex (m, sp) -> quote_sp l (Meta m) sp
  | VRigid (x, sp) -> quote_sp l (Var (ix_of_lvl l x)) sp
  | VLam (x, Closure (env, body)) ->
      Lam (x, quote (l + 1) (Eval.eval (VRigid (l, []) :: env) body))
  | VPi (x, a, Closure (env, body)) ->
      Pi (x, quote l a, quote (l + 1) (Eval.eval (VRigid (l, []) :: env) body))
  | VU -> U
  | VUnit -> Unit
  | VUnitTerm -> UnitTerm
  | VProd (a, b) -> Prod (quote l a, quote l b)
  | VPair (a, b) -> Pair (quote l a, quote l b)

let nf (env : env) (t : tm) : tm = quote (List.length env) (Eval.eval env t)
