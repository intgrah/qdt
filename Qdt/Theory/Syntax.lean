module

public import Qdt.Tele
public import Qdt.Theory.Universe

@[expose] public section

namespace Qdt

open Lean (Name)

/-- de Bruijn indices -/
def Idx n := Fin n
deriving Repr, Hashable, DecidableEq

/-- Allow natural number literals to be used as de Bruijn indices -/
instance {n} [NeZero n] {i} : OfNat (Idx n) i where
  ofNat := Fin.ofNat n i

mutual

/-- Types -/
inductive Ty : Nat → Type
  | u {n} : Universe → Ty n
  | pi {n} : Name → Ty n → Ty (n + 1) → Ty n
  /-- If Γ ⊢ t : .u i, then Γ ⊢ .el t type -/
  | el {n} : Tm n → Ty n
with
  @[computed_field]
  hash' : ∀ n, Ty n → UInt64
    | _, .u u =>
      0 |> mixHash (hash u)
    | _, .pi name dom cod =>
      0 |> mixHash (hash name) |> mixHash dom.hash' |> mixHash cod.hash'
    | _, .el t =>
      1 |> mixHash t.hash'
deriving Repr

/-- Terms -/
inductive Tm : Nat → Type
  | u' {n} : Universe → Tm n
  | var {n} : Idx n → Tm n
  | const {n} : Name → List Universe → Tm n
  | lam {n} : Name → Ty n → Tm (n + 1) → Tm n
  | app {n} : Tm n → Tm n → Tm n
  | pi' {n} : Name → Tm n → Tm (n + 1) → Tm n
  | proj {n} : Nat → Tm n → Tm n
  | letE {n} : Name → Ty n → Tm n → Tm (n + 1) → Tm n
with
  @[computed_field]
  hash' : ∀ n, Tm n → UInt64
    | _, .u' u =>
      0 |> mixHash (hash u)
    | _, .var i =>
      1 |> mixHash (hash i)
    | _, .const name us =>
      2 |> mixHash (hash name) |> mixHash (hash us)
    | _, .lam name ty b =>
      3 |> mixHash (hash name) |> mixHash ty.hash' |> mixHash b.hash'
    | _, .app f a =>
      4 |> mixHash f.hash' |> mixHash a.hash'
    | _, .pi' name a b =>
      5 |> mixHash (hash name) |> mixHash a.hash' |> mixHash b.hash'
    | _, .proj i t =>
      6 |> mixHash (hash i) |> mixHash t.hash'
    | _, .letE name ty rhs body =>
      7 |> mixHash (hash name) |> mixHash ty.hash' |> mixHash rhs.hash' |> mixHash body.hash'
deriving Repr

end

instance {n} : Hashable (Ty n) := ⟨Ty.hash' n⟩
instance {n} : Hashable (Tm n) := ⟨Tm.hash' n⟩
instance {n} : Inhabited (Ty n) := ⟨.u .zero⟩
instance {n} : Inhabited (Tm n) := ⟨.u' .zero⟩

def Ctx := Tele (Name × Ty ·)

instance {a b} : Hashable (Ctx a b) := ⟨Tele.hash⟩

abbrev Ty.arrow {n} (ty : Ty n) := Ty.pi .anonymous ty

@[match_pattern]
def Tm.apps {n} : Tm n → List (Tm n) → Tm n :=
  List.foldl Tm.app

def Ty.pis {a b} : Ctx a b → Ty b → Ty a
  | .nil => id
  | .snoc bs (name, ty) => pis bs ∘ pi name ty

def Ty.getResultUniverse? {n} : Ty n → Option Universe
  | .u univ => some univ
  | .pi _ _ cod => cod.getResultUniverse?
  | .el _ => none

def Tm.lams {a b} : Ctx a b → Tm b → Tm a
  | .nil => id
  | .snoc bs (name, ty) => lams bs ∘ lam name ty

mutual

def Universe.subst (subst : List (Name × Universe)) : Universe → Universe
  | .level n => subst.lookup n |>.getD (.level n)
  | .zero => .zero
  | .succ u => (u.subst subst).mkSucc
  | .max u v => (u.subst subst).mkMax (v.subst subst)

def Ty.substLevels {n} (subst : List (Name × Universe)) : Ty n → Ty n
  | .u u => .u (u.subst subst)
  | .pi name ty b => .pi name (ty.substLevels subst) (b.substLevels subst)
  | .el t => .el (t.substLevels subst)

def Tm.substLevels {n} (subst : List (Name × Universe)) : Tm n → Tm n
  | .u' u => .u' (u.subst subst)
  | .var i => .var i
  | .const c us => .const c (us.map (·.subst subst))
  | .lam name ty b => .lam name (ty.substLevels subst) (b.substLevels subst)
  | .app f a => .app (f.substLevels subst) (a.substLevels subst)
  | .pi' name a b => .pi' name (a.substLevels subst) (b.substLevels subst)
  | .proj i t => .proj i (t.substLevels subst)
  | .letE name ty rhs body =>
      .letE name (ty.substLevels subst) (rhs.substLevels subst) (body.substLevels subst)

end

end Qdt
