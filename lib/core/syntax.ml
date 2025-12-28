(* ========== Core Syntax ========== *)

module Idx = struct
  type t = Idx of int

  let to_int (Idx l) = l
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
