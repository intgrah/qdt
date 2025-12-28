module Lvl : sig
  type t = Lvl of int

  val to_int : t -> int
end

type vty =
  | VTyU
  | VTyPi of string option * vty * clos_ty
  | VTyEl of neutral

and vtm =
  | VTmNeutral of neutral
  | VTmLam of string option * vty * clos_tm
  | VTmPiHat of string option * vtm * clos_tm

and neutral = head * spine

and head =
  | HVar of Lvl.t
  | HConst of Name.t
  | HSorry of int * vty

and spine = vtm list
and clos_ty = ClosTy of env * Syntax.ty
and clos_tm = ClosTm of env * Syntax.tm
and env = vtm list
