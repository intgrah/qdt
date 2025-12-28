open Syntax

let ( |- ) fn arg = TmApp (fn, arg)
let ( |-- ) = List.fold_left ( |- )
let ( @-> ) (name, ty) body = TyPi (name, ty, body)
let ( @--> ) = List.fold_right ( @-> )
let ( @=> ) (name, ty) body = TmLam (name, ty, body)
let ( @==> ) = List.fold_right ( @=> )
let vars n depth = List.init n (fun i -> TmVar (Idx (depth + n - 1 - i)))

let rec shift_ty (d : int) (cutoff : int) : ty -> ty = function
  | TyU -> TyU
  | TyPi (x, a, b) -> TyPi (x, shift_ty d cutoff a, shift_ty d (cutoff + 1) b)
  | TyEl t -> TyEl (shift_tm d cutoff t)

and shift_tm (d : int) (cutoff : int) : tm -> tm = function
  | TmVar (Idx k) ->
      if k < cutoff then
        TmVar (Idx k)
      else
        TmVar (Idx (k + d))
  | TmConst name -> TmConst name
  | TmLam (x, a, body) ->
      TmLam (x, shift_ty d cutoff a, shift_tm d (cutoff + 1) body)
  | TmApp (f, a) -> TmApp (shift_tm d cutoff f, shift_tm d cutoff a)
  | TmPiHat (x, a, b) ->
      TmPiHat (x, shift_tm d cutoff a, shift_tm d (cutoff + 1) b)
  | TmSorry (id, ty) -> TmSorry (id, shift_ty d cutoff ty)
  | TmLet (x, ty, t, body) ->
      TmLet
        ( x,
          shift_ty d cutoff ty,
          shift_tm d cutoff t,
          shift_tm d (cutoff + 1) body )
