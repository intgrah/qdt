module

public import Qdt.Tele
public import Qdt.Theory.Universe

@[expose] public section

namespace Qdt

open Lean (Name)

def Idx n := Fin n
deriving Repr, Hashable, DecidableEq

instance {n} [NeZero n] {i} : OfNat (Idx n) i where
  ofNat := Fin.ofNat n i

abbrev MVarId := Nat

mutual

inductive Ty : Nat → Type
  | u {n} : Universe → Ty n
  | pi {n} : Name → Ty n → Ty (n + 1) → Ty n
  | el {n} : Tm n → Ty n
with
  @[computed_field]
  hash' : ∀ n, Ty n → UInt64
    | _, .u u =>
      0 |> mixHash (hash u)
    | _, .pi name dom cod =>
      1 |> mixHash (hash name) |> mixHash dom.hash' |> mixHash cod.hash'
    | _, .el t =>
      2 |> mixHash t.hash'
deriving Repr

inductive Tm : Nat → Type
  | u' {n} : Universe → Tm n
  | var {n} : Idx n → Tm n
  | const {n} : Name → List Universe → Tm n
  | lam {n} : Name → Ty n → Tm (n + 1) → Tm n
  | app {n} : Tm n → Tm n → Tm n
  | pi' {n} : Name → Tm n → Tm (n + 1) → Tm n
  | proj {n} : Nat → Tm n → Tm n
  | letE {n} : Name → Ty n → Tm n → Tm (n + 1) → Tm n
  | mvar {n} : MVarId → Tm n
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
    | _, .mvar id =>
      8 |> mixHash (hash id)
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

def Tm.splitApps {n} : Tm n → Tm n × List (Tm n)
  | .app f a => let (h, as) := splitApps f; (h, as ++ [a])
  | h => (h, [])

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

def Universe.subst (subst : List Universe) : Universe → Universe
  | .level i => (subst[i]?.getD (.level i)).normalise
  | .zero => .zero
  | .mvar id => .mvar id
  | .succ u => (u.subst subst).mkSucc
  | .max u v => (u.subst subst).mkMax (v.subst subst)

def Ty.substLevels {n} (subst : List Universe) : Ty n → Ty n
  | .u u => .u (u.subst subst)
  | .pi name ty b => .pi name (ty.substLevels subst) (b.substLevels subst)
  | .el t => .el (t.substLevels subst)

def Tm.substLevels {n} (subst : List Universe) : Tm n → Tm n
  | .u' u => .u' (u.subst subst)
  | .var i => .var i
  | .const c us => .const c (us.map (·.subst subst))
  | .lam name ty b => .lam name (ty.substLevels subst) (b.substLevels subst)
  | .app f a => .app (f.substLevels subst) (a.substLevels subst)
  | .pi' name a b => .pi' name (a.substLevels subst) (b.substLevels subst)
  | .proj i t => .proj i (t.substLevels subst)
  | .letE name ty rhs body =>
      .letE name (ty.substLevels subst) (rhs.substLevels subst) (body.substLevels subst)
  | .mvar id => .mvar id

def Ty.shiftLevels {n} (k : Nat) : Ty n → Ty n
  | .u u => .u (u.shift k)
  | .pi name ty b => .pi name (ty.shiftLevels k) (b.shiftLevels k)
  | .el t => .el (t.shiftLevels k)

def Tm.shiftLevels {n} (k : Nat) : Tm n → Tm n
  | .u' u => .u' (u.shift k)
  | .var i => .var i
  | .const c us => .const c (us.map (·.shift k))
  | .lam name ty b => .lam name (ty.shiftLevels k) (b.shiftLevels k)
  | .app f a => .app (f.shiftLevels k) (a.shiftLevels k)
  | .pi' name a b => .pi' name (a.shiftLevels k) (b.shiftLevels k)
  | .proj i t => .proj i (t.shiftLevels k)
  | .letE name ty rhs body =>
      .letE name (ty.shiftLevels k) (rhs.shiftLevels k) (body.shiftLevels k)
  | .mvar id => .mvar id

def Ty.usedLevels {n} : Ty n → List Nat
  | .u u => u.usedLevels
  | .pi _ ty b => ty.usedLevels ++ b.usedLevels
  | .el t => t.usedLevels

def Tm.usedLevels {n} : Tm n → List Nat
  | .u' u => u.usedLevels
  | .var _ => []
  | .const _ us => us.flatMap Universe.usedLevels
  | .lam _ ty b => ty.usedLevels ++ b.usedLevels
  | .app f a => f.usedLevels ++ a.usedLevels
  | .pi' _ a b => a.usedLevels ++ b.usedLevels
  | .proj _ t => t.usedLevels
  | .letE _ ty rhs body => ty.usedLevels ++ rhs.usedLevels ++ body.usedLevels
  | .mvar _ => []

def Ty.hasUMVar {n} : Ty n → Bool
  | .u u => u.hasMVar
  | .pi _ ty b => ty.hasUMVar || b.hasUMVar
  | .el t => t.hasUMVar

def Tm.hasUMVar {n} : Tm n → Bool
  | .u' u => u.hasMVar
  | .var _ => false
  | .const _ us => us.any Universe.hasMVar
  | .lam _ ty b => ty.hasUMVar || b.hasUMVar
  | .app f a => f.hasUMVar || a.hasUMVar
  | .pi' _ a b => a.hasUMVar || b.hasUMVar
  | .proj _ t => t.hasUMVar
  | .letE _ ty rhs body => ty.hasUMVar || rhs.hasUMVar || body.hasUMVar
  | .mvar _ => false

def Ty.freeUMVars {n} : Ty n → List UMVarId
  | .u u => u.freeMVars
  | .pi _ ty b => ty.freeUMVars ++ b.freeUMVars
  | .el t => t.freeUMVars

def Tm.freeUMVars {n} : Tm n → List UMVarId
  | .u' u => u.freeMVars
  | .var _ => []
  | .const _ us => us.flatMap Universe.freeMVars
  | .lam _ ty b => ty.freeUMVars ++ b.freeUMVars
  | .app f a => f.freeUMVars ++ a.freeUMVars
  | .pi' _ a b => a.freeUMVars ++ b.freeUMVars
  | .proj _ t => t.freeUMVars
  | .letE _ ty rhs body => ty.freeUMVars ++ rhs.freeUMVars ++ body.freeUMVars
  | .mvar _ => []

def Ty.substUMVars {n} (f : UMVarId → Option Universe) : Ty n → Ty n
  | .u u => .u (u.substMVars f)
  | .pi name ty b => .pi name (ty.substUMVars f) (b.substUMVars f)
  | .el t => .el (t.substUMVars f)

def Tm.substUMVars {n} (f : UMVarId → Option Universe) : Tm n → Tm n
  | .u' u => .u' (u.substMVars f)
  | .var i => .var i
  | .const c us => .const c (us.map (·.substMVars f))
  | .lam name ty b => .lam name (ty.substUMVars f) (b.substUMVars f)
  | .app fn a => .app (fn.substUMVars f) (a.substUMVars f)
  | .pi' name a b => .pi' name (a.substUMVars f) (b.substUMVars f)
  | .proj i t => .proj i (t.substUMVars f)
  | .letE name ty rhs body =>
      .letE name (ty.substUMVars f) (rhs.substUMVars f) (body.substUMVars f)
  | .mvar id => .mvar id

def Ty.extendConstUnivs {n} (extras : List Universe) (name : Name) : Ty n → Ty n
  | .u u => .u u
  | .pi nm ty b => .pi nm (ty.extendConstUnivs extras name) (b.extendConstUnivs extras name)
  | .el t => .el (t.extendConstUnivs extras name)

def Tm.extendConstUnivs {n} (extras : List Universe) (name : Name) : Tm n → Tm n
  | .u' u => .u' u
  | .var i => .var i
  | .const c us =>
      if c == name then .const c (us ++ extras) else .const c us
  | .lam nm ty b => .lam nm (ty.extendConstUnivs extras name) (b.extendConstUnivs extras name)
  | .app fn a => .app (fn.extendConstUnivs extras name) (a.extendConstUnivs extras name)
  | .pi' nm a b => .pi' nm (a.extendConstUnivs extras name) (b.extendConstUnivs extras name)
  | .proj i t => .proj i (t.extendConstUnivs extras name)
  | .letE nm ty rhs body =>
      .letE nm (ty.extendConstUnivs extras name) (rhs.extendConstUnivs extras name)
        (body.extendConstUnivs extras name)
  | .mvar id => .mvar id

end

mutual

def Ty.Bounded (k : Nat) {n : Nat} : Ty n → Prop
  | .u u => Universe.Bounded k u
  | .el t => Tm.Bounded k t
  | .pi _ A B => Ty.Bounded k A ∧ Ty.Bounded k B

def Tm.Bounded (k : Nat) {n : Nat} : Tm n → Prop
  | .u' u => Universe.Bounded k u
  | .var _ => True
  | .const _ us => ∀ u ∈ us, Universe.Bounded k u
  | .lam _ A b => Ty.Bounded k A ∧ Tm.Bounded k b
  | .app f a => Tm.Bounded k f ∧ Tm.Bounded k a
  | .pi' _ a b => Tm.Bounded k a ∧ Tm.Bounded k b
  | .proj _ t => Tm.Bounded k t
  | .letE _ A e b => Ty.Bounded k A ∧ Tm.Bounded k e ∧ Tm.Bounded k b
  | .mvar _ => True

end

theorem Universe.Bounded.subst {k : Nat} {us : List Universe}
    (hus : ∀ u ∈ us, Universe.Bounded k u) :
    ∀ {u : Universe}, u.Bounded us.length → (u.subst us).Bounded k
  | .level i, h => by
      change (us[i]?.getD (.level i)).normalise.Bounded k
      have hSome : us[i]? = some us[i] := List.getElem?_eq_getElem h
      rw [hSome]
      exact Universe.Bounded.normalise (hus _ (List.getElem_mem h))
  | .zero, _ => trivial
  | .mvar _, _ => trivial
  | .succ u, h => Universe.mkSucc_bounded (Universe.Bounded.subst hus (u := u) h)
  | .max u v, ⟨hu, hv⟩ =>
      Universe.mkMax_bounded
        (Universe.Bounded.subst hus hu)
        (Universe.Bounded.subst hus hv)

end Qdt
