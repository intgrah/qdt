(* ========== Raw Syntax ========== *)

type raw =
  | RIdent of string
  | RApp of raw * raw
  | RLam of string option * raw option * raw
  | RPi of string option * raw * raw
  | RArrow of raw * raw
  | RLet of string * raw option * raw * raw
  | RU
  | RUnit
  | RUnitTm
  | REq of raw * raw
  | RRefl of raw
  | RSigma of string option * raw * raw
  | RProd of raw * raw
  | RPair of raw * raw
  | RProj1 of raw
  | RProj2 of raw
  | RInt
  | RIntLit of int
  | RAdd of raw * raw
  | RAnn of raw * raw

type raw_def = string * raw (* All defs generate an RAnn *)
type raw_program = raw_def list

(* ========== Core Syntax ========== *)

type lvl = int

type ty =
  | TyU
  | TyPi of string option * ty * ty
  | TyArrow of ty * ty
  | TySigma of string option * ty * ty
  | TyProd of ty * ty
  | TyUnit
  | TyInt
  | TyEq of tm * tm * ty
  | TyEl of tm

and tm =
  | TmVar of lvl
  | TmLam of string option * ty * ty * tm
  | TmApp of tm * tm
  | TmPiHat of string option * tm * tm
  | TmArrowHat of tm * tm
  | TmSigmaHat of string option * tm * tm
  | TmProdHat of tm * tm
  | TmMkSigma of ty * ty * tm * tm
  | TmProj1 of tm
  | TmProj2 of tm
  | TmUnit
  | TmIntLit of int
  | TmUnitHat
  | TmIntHat
  | TmEqHat of tm * tm * tm
  | TmRefl of ty * tm
  | TmAdd of tm * tm

type vl_ty =
  | VTyU
  | VTyPi of string option * vl_ty * clos_ty
  | VTyArrow of vl_ty * vl_ty
  | VTySigma of string option * vl_ty * clos_ty
  | VTyProd of vl_ty * vl_ty
  | VTyUnit
  | VTyInt
  | VTyEq of vl_tm * vl_tm * vl_ty
  | VTyEl of neutral

and head =
  | HVar of lvl
  | HGlobal of string

and neutral = head * spine

and vl_tm =
  | VTmNeutral of neutral
  | VTmLam of string option * vl_ty * clos_tm
  | VTmPiHat of string option * vl_tm * clos_tm
  | VTmArrowHat of vl_tm * vl_tm
  | VTmSigmaHat of string option * vl_tm * clos_tm
  | VTmProdHat of vl_tm * vl_tm
  | VTmMkSigma of string option * vl_ty * clos_ty * vl_tm * vl_tm
  | VTmUnit
  | VTmIntLit of int
  | VTmUnitHat
  | VTmIntHat
  | VTmEqHat of vl_tm * vl_tm * vl_tm
  | VTmRefl of vl_ty * vl_tm
  | VTmAdd of vl_tm * vl_tm

and spine = fname list

and fname =
  | FApp of vl_tm
  | FProj1
  | FProj2

and clos_ty = ClosTy of env * ty
and clos_tm = ClosTm of env * tm
and env = vl_tm list
