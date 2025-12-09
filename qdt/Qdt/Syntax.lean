namespace Qdt

abbrev Name := Option String

inductive Raw where
  | ident : String → Raw
  | app : Raw → Raw → Raw
  | lam : List (Name × Option Raw) → Raw → Raw
  | pi : List Name × Raw → Raw → Raw
  | arrow : Raw → Raw → Raw
  | «let» : String → Option Raw → Raw → Raw → Raw
  | u : Raw
  | unit : Raw
  | unitTm : Raw
  | empty : Raw
  | absurd : Raw → Raw
  | eq : Raw → Raw → Raw
  | refl : Raw → Raw
  | sigma : List Name × Raw → Raw → Raw
  | prod : Raw → Raw → Raw
  | pair : Raw → Raw → Raw
  | proj1 : Raw → Raw
  | proj2 : Raw → Raw
  | int : Raw
  | intLit : Int → Raw
  | add : Raw → Raw → Raw
  | sub : Raw → Raw → Raw
  | ann : Raw → Raw → Raw
  | sorry : Raw
  deriving Repr, Inhabited

inductive RawItem where
  | defn : String → Raw → RawItem
  | example : Raw → RawItem
  deriving Repr, Inhabited

abbrev RawProgram := List RawItem

mutual
  inductive Ty where
    | u : Ty
    | pi : Name → Ty → Ty → Ty
    | sigma : Name → Ty → Ty → Ty
    | unit : Ty
    | empty : Ty
    | int : Ty
    | eq : Tm → Tm → Ty → Ty
    | el : Tm → Ty
  deriving Inhabited, Repr

  inductive Tm where
    | var : Nat → Tm
    | const : String → Tm
    | lam : Name → Ty → Tm → Tm
    | app : Tm → Tm → Tm
    | piHat : Name → Tm → Tm → Tm
    | sigmaHat : Name → Tm → Tm → Tm
    | mkSigma : Ty → Ty → Tm → Tm → Tm
    | proj1 : Tm → Tm
    | proj2 : Tm → Tm
    | unit : Tm
    | absurd : Ty → Tm → Tm
    | intLit : Int → Tm
    | unitHat : Tm
    | emptyHat : Tm
    | intHat : Tm
    | eqHat : Tm → Tm → Ty → Tm
    | refl : Ty → Tm → Tm
    | add : Tm → Tm → Tm
    | sub : Tm → Tm → Tm
    | sorry : Nat → Ty → Tm
    | «let» : String → Ty → Tm → Tm → Tm
  deriving Inhabited, Repr
end

mutual
  inductive Head where
    | var : Nat → Head
    | const : String → Head
    | sorry : Nat → VTy → Head
    deriving Repr, Inhabited

  inductive Frame where
    | app : VTm → Frame
    | proj1 : Frame
    | proj2 : Frame
    | absurd : VTy → Frame

  inductive Neutral where
    | mk : Head → List Frame → Neutral

  inductive VTy where
    | u : VTy
    | pi : Name → VTy → Env → Ty → VTy
    | sigma : Name → VTy → Env → Ty → VTy
    | unit : VTy
    | empty : VTy
    | int : VTy
    | eq : VTm → VTm → VTy → VTy
    | el : Neutral → VTy

  inductive VTm where
    | neutral : Neutral → VTm
    | lam : Name → VTy → Env → Tm → VTm
    | piHat : Name → VTm → Env → Tm → VTm
    | sigmaHat : Name → VTm → Env → Tm → VTm
    | mkSigma : Name → VTy → Env → Ty → VTm → VTm → VTm
    | unit : VTm
    | intLit : Int → VTm
    | unitHat : VTm
    | emptyHat : VTm
    | intHat : VTm
    | eqHat : VTm → VTm → VTy → VTm
    | refl : VTy → VTm → VTm
    | add : VTm → VTm → VTm
    | sub : VTm → VTm → VTm

  inductive Env where
    | nil : Env
    | cons : VTm → Env → Env
end

def Neutral.head : Neutral → Head
  | .mk h _ => h

def Neutral.spine : Neutral → List Frame
  | .mk _ sp => sp

def Neutral.snoc (n : Neutral) (f : Frame) : Neutral :=
  .mk n.head (n.spine ++ [f])

def Env.toList : Env → List VTm
  | .nil => []
  | .cons v env => v :: env.toList

def Env.length : Env → Nat
  | .nil => 0
  | .cons _ env => env.length + 1

def Env.get? : Env → Nat → Option VTm
  | .nil, _ => none
  | .cons v _, 0 => some v
  | .cons _ env, n + 1 => env.get? n

instance : Inhabited Frame where default := .proj1
instance : Inhabited Neutral where default := .mk (.var 0) []
instance : Inhabited VTy where default := .u
instance : Inhabited VTm where default := .unit
instance : Inhabited Env where default := .nil

end Qdt
