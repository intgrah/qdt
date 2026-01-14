import Qdt.Tele
import Qdt.MLTT.Universe

namespace Qdt

open Lean (Name)

/-- de Bruijn indices -/
def Idx n := Fin n
deriving Repr, Hashable, DecidableEq, BEq

/-- Allow natural number literals to be used as de Bruijn indices -/
instance {n} [NeZero n] {i} : OfNat (Idx n) i where
  ofNat := Fin.ofNat n i

mutual

/-- Types -/
inductive Ty : Nat → Type
  | u {n} : Universe → Ty n
  | pi {n} : Param n → Ty (n + 1) → Ty n
  /-- If Γ ⊢ t : 𝑢 i, then Γ ⊢ El(t) type -/
  | el {n} : Tm n → Ty n
deriving Repr, Hashable, DecidableEq, BEq

inductive Tm : Nat → Type
  | u' {n} : Universe → Tm n
  | var {n} : Idx n → Tm n
  | const {n} : Name → List Universe → Tm n
  | lam {n} : Param n → Tm (n + 1) → Tm n
  | app {n} : Tm n → Tm n → Tm n
  | pi' {n} : Name → Tm n → Tm (n + 1) → Tm n
  | proj {n} : Nat → Tm n → Tm n
  | letE {n} : Name → Ty n → Tm n → Tm (n + 1) → Tm n
deriving Repr, Hashable, DecidableEq, BEq

@[pp_using_anonymous_constructor]
inductive Param : Nat → Type
  | mk {n} (name : Name) (ty : Ty n) : Param n
deriving Repr, Hashable, DecidableEq, BEq

end

notation "𝑢" => Ty.u

abbrev Ty.arrow {n} (ty : Ty n) := Ty.pi ⟨.anonymous, ty⟩

@[match_pattern]
def Tm.apps {n} : Tm n → List (Tm n) → Tm n :=
  List.foldl Tm.app

/- Point free! Point free! -/
def Ty.pis {a b} : Tele Param a b → Ty b → Ty a
  | .nil => id
  | .snoc bs param => pis bs ∘ pi param

def Ty.getResultUniverse? {n} : Ty n → Option Universe
  | .u univ => some univ
  | .pi _ cod => cod.getResultUniverse?
  | .el _ => none

def Tm.lams {a b} : Tele Param a b → Tm b → Tm a
  | .nil => id
  | .snoc bs param => lams bs ∘ lam param

private def lookup (subst : List (Name × Universe)) (n : Name) : Universe :=
  match subst.find? (·.fst == n) with
  | some (_, u) => u
  | none => .level n

mutual

def Universe.subst (subst : List (Name × Universe)) : Universe → Universe
  | .level n => lookup subst n
  | .zero => .zero
  | .succ u => .succ (u.subst subst)
  | .max u v => .max (u.subst subst) (v.subst subst)

def Ty.substLevels {n} (subst : List (Name × Universe)) : Ty n → Ty n
  | .u u => .u (u.subst subst)
  | .pi ⟨name, ty⟩ b => .pi ⟨name, ty.substLevels subst⟩ (b.substLevels subst)
  | .el t => .el (t.substLevels subst)

def Tm.substLevels {n} (subst : List (Name × Universe)) : Tm n → Tm n
  | .u' u => .u' (u.subst subst)
  | .var i => .var i
  | .const c us => .const c (us.map (·.subst subst))
  | .lam ⟨name, ty⟩ b => .lam ⟨name, ty.substLevels subst⟩ (b.substLevels subst)
  | .app f a => .app (f.substLevels subst) (a.substLevels subst)
  | .pi' name a b => .pi' name (a.substLevels subst) (b.substLevels subst)
  | .proj i t => .proj i (t.substLevels subst)
  | .letE name ty rhs body =>
      .letE name (ty.substLevels subst) (rhs.substLevels subst) (body.substLevels subst)

def Param.substLevels {n} (subst : List (Name × Universe)) : Param n → Param n
  | ⟨name, ty⟩ => ⟨name, ty.substLevels subst⟩

end

mutual

def Ty.levelNames {n} : Ty n → List Name
  | .u u => u.levelNames
  | .pi ⟨_, ty⟩ b => ty.levelNames ++ b.levelNames
  | .el t => t.levelNames

def Tm.levelNames {n} : Tm n → List Name
  | .u' u => u.levelNames
  | .var _ => []
  | .const _ us => us.flatMap Universe.levelNames
  | .lam ⟨_, ty⟩ b => ty.levelNames ++ b.levelNames
  | .app f a => f.levelNames ++ a.levelNames
  | .pi' _ a b => a.levelNames ++ b.levelNames
  | .proj _ t => t.levelNames
  | .letE _ ty rhs body => ty.levelNames ++ rhs.levelNames ++ body.levelNames

def Param.levelNames {n} : Param n → List Name
  | ⟨_, ty⟩ => ty.levelNames

end

end Qdt
