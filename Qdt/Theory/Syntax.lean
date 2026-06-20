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

inductive BinderInfo
  | explicit
  | implicit
deriving Repr, Hashable, DecidableEq, BEq, Inhabited

mutual

inductive Ty : Nat → Type
  | u {n} : Universe → Ty n
  | pi {n} : Name → BinderInfo → Ty n → Ty (n + 1) → Ty n
  | el {n} : Tm n → Ty n
with
  @[computed_field]
  hash' : ∀ n, Ty n → UInt64
    | _, .u u =>
      0 |> mixHash (hash u)
    | _, .pi name bi dom cod =>
      1 |> mixHash (hash name) |> mixHash (hash bi) |> mixHash dom.hash' |> mixHash cod.hash'
    | _, .el t =>
      2 |> mixHash t.hash'
deriving Repr

inductive Tm : Nat → Type
  | u' {n} : Universe → Tm n
  | var {n} : Idx n → Tm n
  | const {n} : Name → List Universe → Tm n
  | lam {n} : Name → BinderInfo → Ty n → Tm (n + 1) → Tm n
  | app {n} : Tm n → Tm n → Tm n
  | pi' {n} : Name → BinderInfo → Tm n → Tm (n + 1) → Tm n
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
    | _, .lam name bi ty b =>
      3 |> mixHash (hash name) |> mixHash (hash bi) |> mixHash ty.hash' |> mixHash b.hash'
    | _, .app f a =>
      4 |> mixHash f.hash' |> mixHash a.hash'
    | _, .pi' name bi a b =>
      5 |> mixHash (hash name) |> mixHash (hash bi) |> mixHash a.hash' |> mixHash b.hash'
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

def Ctx := Tele (Name × BinderInfo × Ty ·)

instance {a b} : Hashable (Ctx a b) := ⟨Tele.hash⟩

def Ctx.toImplicit {a b : Nat} (ctx : Ctx a b) : Ctx a b :=
  ctx.map fun {n : Nat} (name, _, ty) => ((name, BinderInfo.implicit, ty) : Name × BinderInfo × Ty n)

abbrev Ty.arrow {n} (ty : Ty n) := Ty.pi .anonymous .explicit ty

@[match_pattern]
def Tm.apps {n} : Tm n → List (Tm n) → Tm n :=
  List.foldl Tm.app

def Tm.splitApps {n} : Tm n → Tm n × List (Tm n)
  | .app f a => let (h, as) := splitApps f; (h, as ++ [a])
  | h => (h, [])

def Ty.pis {a b} : Ctx a b → Ty b → Ty a
  | .nil => id
  | .snoc bs (name, bi, ty) => pis bs ∘ pi name bi ty

def Ty.getResultUniverse? {n} : Ty n → Option Universe
  | .u univ => some univ
  | .pi _ _ _ cod => cod.getResultUniverse?
  | .el _ => none

def Tm.lams {a b} : Ctx a b → Tm b → Tm a
  | .nil => id
  | .snoc bs (name, bi, ty) => lams bs ∘ lam name bi ty

mutual

def Ty.substParams {n} (σ : Name → Option Universe) : Ty n → Ty n
  | .u u => .u (u.subst σ)
  | .pi name bi ty b => .pi name bi (ty.substParams σ) (b.substParams σ)
  | .el t => .el (t.substParams σ)

def Tm.substParams {n} (σ : Name → Option Universe) : Tm n → Tm n
  | .u' u => .u' (u.subst σ)
  | .var i => .var i
  | .const c us => .const c (us.map (·.subst σ))
  | .lam name bi ty b => .lam name bi (ty.substParams σ) (b.substParams σ)
  | .app f a => .app (f.substParams σ) (a.substParams σ)
  | .pi' name bi a b => .pi' name bi (a.substParams σ) (b.substParams σ)
  | .proj i t => .proj i (t.substParams σ)
  | .letE name ty rhs body =>
      .letE name (ty.substParams σ) (rhs.substParams σ) (body.substParams σ)
  | .mvar id => .mvar id

def Ty.usedParams {n} : Ty n → List Name
  | .u u => u.usedParams
  | .pi _ _ ty b => ty.usedParams ++ b.usedParams
  | .el t => t.usedParams

def Tm.usedParams {n} : Tm n → List Name
  | .u' u => u.usedParams
  | .var _ => []
  | .const _ us => us.flatMap Universe.usedParams
  | .lam _ _ ty b => ty.usedParams ++ b.usedParams
  | .app f a => f.usedParams ++ a.usedParams
  | .pi' _ _ a b => a.usedParams ++ b.usedParams
  | .proj _ t => t.usedParams
  | .letE _ ty rhs body => ty.usedParams ++ rhs.usedParams ++ body.usedParams
  | .mvar _ => []

def Ty.hasUMVar {n} : Ty n → Bool
  | .u u => u.hasMVar
  | .pi _ _ ty b => ty.hasUMVar || b.hasUMVar
  | .el t => t.hasUMVar

def Tm.hasUMVar {n} : Tm n → Bool
  | .u' u => u.hasMVar
  | .var _ => false
  | .const _ us => us.any Universe.hasMVar
  | .lam _ _ ty b => ty.hasUMVar || b.hasUMVar
  | .app f a => f.hasUMVar || a.hasUMVar
  | .pi' _ _ a b => a.hasUMVar || b.hasUMVar
  | .proj _ t => t.hasUMVar
  | .letE _ ty rhs body => ty.hasUMVar || rhs.hasUMVar || body.hasUMVar
  | .mvar _ => false

def Ty.occursVar {n} (d : Nat) : Ty n → Bool
  | .u _ => false
  | .pi _ _ ty b => ty.occursVar d || b.occursVar (d + 1)
  | .el t => t.occursVar d

def Tm.occursVar {n} (d : Nat) : Tm n → Bool
  | .u' _ => false
  | .var i => i.val == d
  | .const _ _ => false
  | .lam _ _ ty b => ty.occursVar d || b.occursVar (d + 1)
  | .app f a => f.occursVar d || a.occursVar d
  | .pi' _ _ ty b => ty.occursVar d || b.occursVar (d + 1)
  | .proj _ t => t.occursVar d
  | .letE _ ty rhs b => ty.occursVar d || rhs.occursVar d || b.occursVar (d + 1)
  | .mvar _ => false

def Ty.freeUMVars {n} : Ty n → List UMVarId
  | .u u => u.freeMVars
  | .pi _ _ ty b => ty.freeUMVars ++ b.freeUMVars
  | .el t => t.freeUMVars

def Tm.freeUMVars {n} : Tm n → List UMVarId
  | .u' u => u.freeMVars
  | .var _ => []
  | .const _ us => us.flatMap Universe.freeMVars
  | .lam _ _ ty b => ty.freeUMVars ++ b.freeUMVars
  | .app f a => f.freeUMVars ++ a.freeUMVars
  | .pi' _ _ a b => a.freeUMVars ++ b.freeUMVars
  | .proj _ t => t.freeUMVars
  | .letE _ ty rhs body => ty.freeUMVars ++ rhs.freeUMVars ++ body.freeUMVars
  | .mvar _ => []

def Ty.substUMVars {n} (f : UMVarId → Option Universe) : Ty n → Ty n
  | .u u => .u (u.substMVars f)
  | .pi name bi ty b => .pi name bi (ty.substUMVars f) (b.substUMVars f)
  | .el t => .el (t.substUMVars f)

def Tm.substUMVars {n} (f : UMVarId → Option Universe) : Tm n → Tm n
  | .u' u => .u' (u.substMVars f)
  | .var i => .var i
  | .const c us => .const c (us.map (·.substMVars f))
  | .lam name bi ty b => .lam name bi (ty.substUMVars f) (b.substUMVars f)
  | .app fn a => .app (fn.substUMVars f) (a.substUMVars f)
  | .pi' name bi a b => .pi' name bi (a.substUMVars f) (b.substUMVars f)
  | .proj i t => .proj i (t.substUMVars f)
  | .letE name ty rhs body =>
      .letE name (ty.substUMVars f) (rhs.substUMVars f) (body.substUMVars f)
  | .mvar id => .mvar id

def Ty.extendConstUnivs {n} (extras : List Universe) (name : Name) : Ty n → Ty n
  | .u u => .u u
  | .pi nm bi ty b => .pi nm bi (ty.extendConstUnivs extras name) (b.extendConstUnivs extras name)
  | .el t => .el (t.extendConstUnivs extras name)

def Tm.extendConstUnivs {n} (extras : List Universe) (name : Name) : Tm n → Tm n
  | .u' u => .u' u
  | .var i => .var i
  | .const c us =>
      if c == name then .const c (us ++ extras) else .const c us
  | .lam nm bi ty b => .lam nm bi (ty.extendConstUnivs extras name) (b.extendConstUnivs extras name)
  | .app fn a => .app (fn.extendConstUnivs extras name) (a.extendConstUnivs extras name)
  | .pi' nm bi a b => .pi' nm bi (a.extendConstUnivs extras name) (b.extendConstUnivs extras name)
  | .proj i t => .proj i (t.extendConstUnivs extras name)
  | .letE nm ty rhs body =>
      .letE nm (ty.extendConstUnivs extras name) (rhs.extendConstUnivs extras name)
        (body.extendConstUnivs extras name)
  | .mvar id => .mvar id

end

def Ty.instantiateParams {n} (paramNames : List Name) (us : List Universe) : Ty n → Ty n :=
  Ty.substParams (Universe.getParamSubst paramNames us)

def Tm.instantiateParams {n} (paramNames : List Name) (us : List Universe) : Tm n → Tm n :=
  Tm.substParams (Universe.getParamSubst paramNames us)

mutual

def Ty.Bounded (Γ : List Name) {n : Nat} : Ty n → Prop
  | .u u => Universe.Bounded Γ u
  | .el t => Tm.Bounded Γ t
  | .pi _ _ A B => Ty.Bounded Γ A ∧ Ty.Bounded Γ B

def Tm.Bounded (Γ : List Name) {n : Nat} : Tm n → Prop
  | .u' u => Universe.Bounded Γ u
  | .var _ => True
  | .const _ us => ∀ u ∈ us, Universe.Bounded Γ u
  | .lam _ _ A b => Ty.Bounded Γ A ∧ Tm.Bounded Γ b
  | .app f a => Tm.Bounded Γ f ∧ Tm.Bounded Γ a
  | .pi' _ _ a b => Tm.Bounded Γ a ∧ Tm.Bounded Γ b
  | .proj _ t => Tm.Bounded Γ t
  | .letE _ A e b => Ty.Bounded Γ A ∧ Tm.Bounded Γ e ∧ Tm.Bounded Γ b
  | .mvar _ => True

end

theorem Universe.Bounded.subst {Γ Δ : List Name} {σ : Name → Option Universe}
    (hσ : ∀ n ∈ Γ, ∃ u', σ n = some u' ∧ u'.Bounded Δ) :
    ∀ {u : Universe}, u.Bounded Γ → (u.subst σ).Bounded Δ
  | .param n, h => by
      obtain ⟨u', hσn, hu'⟩ := hσ n h
      have : Universe.subst σ (.param n) = u' := by
        simp only [Universe.subst, hσn]
      rw [this]; exact hu'
  | .zero, _ => trivial
  | .mvar _, _ => trivial
  | .succ u, h => Universe.mkSucc_bounded (Universe.Bounded.subst hσ (u := u) h)
  | .max u v, ⟨hu, hv⟩ =>
      Universe.mkMax_bounded
        (Universe.Bounded.subst hσ hu)
        (Universe.Bounded.subst hσ hv)

end Qdt
