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
deriving Repr

/-- Terms -/
inductive Tm : Nat → Type
  | u' {n} : Universe → Tm n
  | var {n} : Idx n → Tm n
  | const {n} : Name → List Universe → Tm n
  | lam {n} : Param n → Tm (n + 1) → Tm n
  | app {n} : Tm n → Tm n → Tm n
  | pi' {n} : Param' n → Tm (n + 1) → Tm n
  | proj {n} : Nat → Tm n → Tm n
  | letE {n} : Name → Ty n → Tm n → Tm (n + 1) → Tm n
deriving Repr

@[pp_using_anonymous_constructor]
inductive Param : Nat → Type
  | mk {n} (name : Name) (ty : Ty n) : Param n
deriving Repr

@[pp_using_anonymous_constructor]
inductive Param' : Nat → Type
  | mk {n} (name : Name) (tm : Tm n) : Param' n
deriving Repr

end

instance {n} : Inhabited (Ty n) := ⟨.u .zero⟩
instance {n} : Inhabited (Tm n) := ⟨.u' .zero⟩
instance {n} : Inhabited (Param n) := ⟨⟨.anonymous, default⟩⟩

def Ctx := Tele Param

notation "𝑢" => Ty.u

abbrev Ty.arrow {n} (ty : Ty n) := Ty.pi ⟨.anonymous, ty⟩

@[match_pattern]
def Tm.apps {n} : Tm n → List (Tm n) → Tm n :=
  List.foldl Tm.app

def Ty.pis {a b} : Ctx a b → Ty b → Ty a
  | .nil => id
  | .snoc bs param => pis bs ∘ pi param

def Ty.getResultUniverse? {n} : Ty n → Option Universe
  | .u univ => some univ
  | .pi _ cod => cod.getResultUniverse?
  | .el _ => none

def Tm.lams {a b} : Ctx a b → Tm b → Tm a
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
  | .pi' ⟨name, a⟩ b => .pi' ⟨name, a.substLevels subst⟩ (b.substLevels subst)
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
  | .pi' ⟨_, a⟩ b => a.levelNames ++ b.levelNames
  | .proj _ t => t.levelNames
  | .letE _ ty rhs body => ty.levelNames ++ rhs.levelNames ++ body.levelNames

def Param.levelNames {n} : Param n → List Name
  | ⟨_, ty⟩ => ty.levelNames

end

/-!
## Hashable instances

Since mutual inductives cannot derive Hashable automatically, we define them manually.
-/

mutual

def Ty.hash {n} : Ty n → UInt64
  | .u u => mixHash 1 (hash u)
  | .pi p b => mixHash 2 (mixHash p.hash b.hash)
  | .el t => mixHash 3 t.hash

def Tm.hash {n} : Tm n → UInt64
  | .u' u => mixHash 10 (hash u)
  | .var i => mixHash 11 (hash i)
  | .const name us => mixHash 12 (mixHash (hash name) (hash us))
  | .lam p body => mixHash 13 (mixHash p.hash body.hash)
  | .app f a => mixHash 14 (mixHash f.hash a.hash)
  | .pi' ⟨name, a⟩ b => mixHash 15 (mixHash (hash name) (mixHash a.hash b.hash))
  | .proj i t => mixHash 16 (mixHash (hash i) t.hash)
  | .letE name ty val body => mixHash 17 (mixHash (hash name) (mixHash ty.hash (mixHash val.hash body.hash)))

def Param.hash {n} : Param n → UInt64
  | ⟨name, ty⟩ => mixHash (hash name) ty.hash

end

instance {n} : Hashable (Ty n) := ⟨Ty.hash⟩
instance {n} : Hashable (Tm n) := ⟨Tm.hash⟩
instance {n} : Hashable (Param n) := ⟨Param.hash⟩

private def hashCtx {a b} : Ctx a b → UInt64
  | .nil => 0
  | .snoc ts t => mixHash (hashCtx ts) (hash t)

instance {a b} : Hashable (Ctx a b) := ⟨hashCtx⟩

end Qdt
