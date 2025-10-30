type ident = string
type ix = Ix of int
type lvl = Lvl of int

(* Concrete syntax *)
type raw =
  | RVar of ident
  | RLam of ident * raw
  | RType
  | RPi of ident * raw * raw
  | RLet of ident * raw * raw * raw

(* Terms and types *)
type t =
  | Var of ix
  | Lam of ident * t
  | App of t * t
  | Type
  | Pi of ident * t * t
  | Let of ident * t * t * t

(* Values *)
type v =
  | VVar of lvl
  | VApp of v * v
  | VLam of ident * closure
  | VPi of ident * v * closure
  | VType

and closure = env * t
and env = v list
