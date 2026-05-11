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

def Universe.subst (subst : List Universe) : Universe → Universe
  | .level i => (subst[i]?.getD (.level i)).normalise
  | .zero => .zero
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

end

theorem Universe.Bounded.subst {k : Nat} {us : List Universe}
    (hus : ∀ u ∈ us, Universe.Bounded k u) :
    ∀ {u : Universe}, u.Bounded us.length → (u.subst us).Bounded k
  | .level i, h => by
      show (us[i]?.getD (.level i)).normalise.Bounded k
      have hi : i < us.length := h
      have hSome : us[i]? = some us[i] := List.getElem?_eq_getElem hi
      rw [hSome]
      exact Universe.Bounded.normalise (hus _ (List.getElem_mem hi))
  | .zero, _ => trivial
  | .succ u, h => by
      show (Universe.subst us u).mkSucc.Bounded k
      exact Universe.mkSucc_bounded (Universe.Bounded.subst hus (u := u) h)
  | .max u v, h => by
      have ⟨hu, hv⟩ : u.Bounded us.length ∧ v.Bounded us.length := h
      show ((Universe.subst us u).mkMax (Universe.subst us v)).Bounded k
      exact Universe.mkMax_bounded
        (Universe.Bounded.subst hus (u := u) hu)
        (Universe.Bounded.subst hus (u := v) hv)

end Qdt
