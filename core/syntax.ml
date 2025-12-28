(* ========== Core Syntax ========== *)

module Idx = struct
  type t = Idx of int

  let to_int (Idx l) = l
end

module Lvl = struct
  type t = Lvl of int

  let to_int (Lvl l) = l
end

type ty =
  | TyU
  | TyPi of string option * ty * ty
  | TyEl of tm

and tm =
  | TmVar of Idx.t
  | TmConst of Name.t
  | TmLam of string option * ty * tm
  | TmApp of tm * tm
  | TmPiHat of string option * tm * tm
  | TmSorry of int * ty
  | TmLet of string * ty * tm * tm

type vl_ty =
  | VTyU
  | VTyPi of string option * vl_ty * clos_ty
  | VTyEl of neutral

and vl_tm =
  | VTmNeutral of neutral
  | VTmLam of string option * vl_ty * clos_tm
  | VTmPiHat of string option * vl_tm * clos_tm

and neutral = head * spine

and head =
  | HVar of Lvl.t (* de Bruijn level *)
  | HConst of Name.t
  | HSorry of int * vl_ty

and spine = vl_tm list
and clos_ty = ClosTy of env * ty
and clos_tm = ClosTm of env * tm
and env = vl_tm list
