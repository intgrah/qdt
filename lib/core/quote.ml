open Syntax
open Semantics

let rec quote_ty (genv : Global.t) (l : int) : vty -> ty = function
  | VTyU -> TyU
  | VTyPi (x, a, ClosTy (env, body)) ->
      let a' = quote_ty genv l a in
      let var = VTmNeutral (HVar (Lvl l), []) in
      let b' = quote_ty genv (l + 1) (Nbe.eval_ty genv (var :: env) body) in
      TyPi (x, a', b')
  | VTyEl n -> TyEl (quote_neutral genv l n)

and quote_tm (genv : Global.t) (l : int) : vtm -> tm = function
  | VTmNeutral n -> quote_neutral genv l n
  | VTmLam (x, a, ClosTm (env, body)) ->
      let var = VTmNeutral (HVar (Lvl l), []) in
      let a = quote_ty genv l a in
      let body' = quote_tm genv (l + 1) (Nbe.eval_tm genv (var :: env) body) in
      TmLam (x, a, body')
  | VTmPiHat (x, a, ClosTm (env, body)) ->
      let a = quote_tm genv l a in
      let var = VTmNeutral (HVar (Lvl l), []) in
      let b = quote_tm genv (l + 1) (Nbe.eval_tm genv (var :: env) body) in
      TmPiHat (x, a, b)

and quote_neutral (genv : Global.t) (l : int) ((head, sp) : neutral) : tm =
  let head =
    match head with
    | HVar (Lvl k) -> TmVar (Idx (l - k - 1))
    | HConst name -> TmConst name
    | HSorry (id, ty) -> TmSorry (id, quote_ty genv l ty)
  in
  List.fold_left (fun head arg -> TmApp (head, quote_tm genv l arg)) head sp

let rec reify_ty (genv : Global.t) (l : int) : vty -> tm = function
  | VTyU -> raise (Failure "Cannot reify Type as a term")
  | VTyPi (x, a, ClosTy (env, b)) ->
      let var = VTmNeutral (HVar (Lvl l), []) in
      let a' = reify_ty genv l a in
      let b_ty = Nbe.eval_ty genv (var :: env) b in
      let b' = reify_ty genv (l + 1) b_ty in
      TmPiHat (x, a', b')
  | VTyEl n -> quote_neutral genv l n
