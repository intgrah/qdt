import Qdt.MLTT.Syntax

namespace Qdt

private def Ren (a b : Nat) := Idx a → Idx b
private def Ren.id (a : Nat) : Ren a a := fun i => i
private def Ren.shift {a} : Ren a (a + 1) := Fin.succ
private def Ren.comp {l m n : Nat} (ξ : Ren l m) (ζ : Ren m n) : Ren l n := ζ ∘ ξ
private theorem Ren.id_comp {m n} (ξ : Ren m n) : Ren.comp (Ren.id m) ξ = ξ := Function.id_comp ξ
private theorem Ren.comp_id {m n}(ξ : Ren m n) : Ren.comp ξ (Ren.id n) = ξ := Function.comp_id ξ
private theorem Ren.comp_assoc {k l m n} (ξ : Ren k l) (ζ : Ren l m) (η : Ren m n) :
    (ξ.comp ζ).comp η = ξ.comp (ζ.comp η) := rfl

private def Ren.cons {a b} (j : Idx b) (ξ : Ren a b) : Ren (a + 1) b
  | ⟨0, _⟩ => j
  | ⟨i + 1, h⟩ => ξ ⟨i, by omega⟩
infixr:67 " .: " => Ren.cons

private def Ren.up {a b} (ξ : Ren a b) : Ren (a + 1) (b + 1) := 0 .: Ren.shift ∘ ξ

mutual
private def Ty.ren {m n : Nat} (ξ : Ren m n) : Ty m → Ty n
  | 𝑢 i => 𝑢 i
  | .pi ⟨x, a⟩ b => .pi ⟨x, a.ren ξ⟩ (b.ren ξ.up)
  | .el t => .el (t.ren ξ)
private def Tm.ren {m n : Nat} (ξ : Ren m n) : Tm m → Tm n
  | .u' i => .u' i
  | .var i => .var (ξ i)
  | .const x us => .const x us
  | .lam ⟨x, a⟩ body => .lam ⟨x, a.ren ξ⟩ (body.ren ξ.up)
  | .app f a => .app (f.ren ξ) (a.ren ξ)
  | .pi' x a b => .pi' x (a.ren ξ) (b.ren ξ.up)
  | .proj i t => .proj i (t.ren ξ)
  | .letE x ty t body => .letE x (ty.ren ξ) (t.ren ξ) (body.ren ξ.up)
end


@[simp]
private theorem Ren.up_id (n : Nat) : (Ren.id n).up = Ren.id (n + 1) := by
  funext ⟨i, hi⟩; cases i <;> rfl

@[simp]
private theorem Ren.up_comp {l m n : Nat} (ξ : Ren l m) (ζ : Ren m n) :
    (ξ.comp ζ).up = ξ.up.comp ζ.up := by
  funext ⟨i, hi⟩; cases i <;> rfl

mutual
@[simp]
private theorem Ty.ren_id {n} : ∀ A : Ty n, A.ren (Ren.id n) = A
  | 𝑢 .. => rfl
  | .pi ⟨_, _⟩ _ => by simp [Ty.ren, Ty.ren_id]
  | .el .. => by simp [Ty.ren, Tm.ren_id]
@[simp]
private theorem Tm.ren_id {n} : ∀ t : Tm n, t.ren (Ren.id n) = t
  | .u' .. => rfl
  | .var .. => rfl
  | .const .. => rfl
  | .lam ⟨_, _⟩ _ => by simp [Tm.ren, Ty.ren_id, Tm.ren_id]
  | .app .. => by simp only [Tm.ren, Tm.ren_id]
  | .pi' .. => by simp [Tm.ren, Tm.ren_id]
  | .proj .. => by simp only [Tm.ren, Tm.ren_id]
  | .letE .. => by simp [Tm.ren, Ty.ren_id, Tm.ren_id]
end

private theorem Ren.shift_comp {m n} (ξ : Ren m n) :
    Ren.shift.comp ξ.up = ξ.comp Ren.shift := rfl

mutual
@[simp]
private theorem Ty.comp_ren {l m n} (ξ : Ren l m) (ζ : Ren m n) :
    ∀ A : Ty l, A.ren (ξ.comp ζ) = (A.ren ξ).ren ζ
  | 𝑢 .. => rfl
  | .pi ⟨_, _⟩ _ => by simp [Ty.ren, Ty.comp_ren]
  | .el .. => by simp only [Ty.ren, Tm.comp_ren]
@[simp]
private theorem Tm.comp_ren {l m n} (ξ : Ren l m) (ζ : Ren m n) :
    ∀ t : Tm l, t.ren (ξ.comp ζ) = (t.ren ξ).ren ζ
  | .u' .. => rfl
  | .var .. => rfl
  | .const .. => rfl
  | .lam ⟨_, _⟩ _ => by simp [Tm.ren, Ty.comp_ren, Tm.comp_ren]
  | .app .. => by simp only [Tm.ren, Tm.comp_ren]
  | .pi' .. => by simp [Tm.ren, Tm.comp_ren]
  | .proj .. => by simp only [Tm.ren, Tm.comp_ren]
  | .letE .. => by simp [Tm.ren, Ty.comp_ren, Tm.comp_ren]
end


def Subst (a b : Nat) := Idx a → Tm b
@[ext] theorem Subst.ext {a b : Nat} {σ τ : Subst a b} : (∀ i, σ i = τ i) →  σ = τ := funext
def Subst.id (a : Nat) : Subst a a := Tm.var
def Subst.shift {a} : Subst a (a + 1) := Subst.id (a + 1) ∘ Ren.shift
def Subst.cons {a b} (s : Tm b) (σ : Subst a b) : Subst (a + 1) b
  | ⟨0, _⟩ => s
  | ⟨i + 1, h⟩ => σ ⟨i, by omega⟩
infixr:67 " .: " => Subst.cons
def Subst.up {m n} (σ : Subst m n) : Subst (m + 1) (n + 1) :=
  Subst.id (n + 1) 0 .: Tm.ren Ren.shift ∘ σ

@[simp]
theorem Subst.up_id (n : Nat) : (Subst.id n).up = Subst.id (n + 1) := by
  funext ⟨i, hi⟩; cases i <;> rfl

mutual
def Ty.subst {m n : Nat} (σ : Subst m n) : Ty m → Ty n
  | 𝑢 i => 𝑢 i
  | .pi ⟨x, a⟩ b => .pi ⟨x, a.subst σ⟩ (b.subst σ.up)
  | .el t => .el (t.subst σ)
def Tm.subst {m n : Nat} (σ : Subst m n) : Tm m → Tm n
  | .u' i => .u' i
  | .var i => σ i
  | .const name us => .const name us
  | .lam ⟨x, a⟩ body => .lam ⟨x, a.subst σ⟩ (body.subst σ.up)
  | .app f a => .app (f.subst σ) (a.subst σ)
  | .pi' x a b => .pi' x (a.subst σ) (b.subst σ.up)
  | .proj i t => .proj i (t.subst σ)
  | .letE x ty t body => .letE x (ty.subst σ) (t.subst σ) (body.subst σ.up)
end

@[simp]
theorem Tm.subst_var {m n : Nat} (σ : Subst m n) (i : Idx m) : Tm.subst σ (.var i) = σ i := rfl

def Subst.comp {l m n : Nat} (σ : Subst l m) (τ : Subst m n) : Subst l n := Tm.subst τ ∘ σ

abbrev Ren.toSubst {m n} (ξ : Ren m n) : Subst m n := Tm.var ∘ ξ

theorem Subst.subst_comp_up {m n} (ξ : Ren m n) :
    ξ.toSubst.up = ξ.up.toSubst := by
  funext ⟨i, hi⟩; cases i <;> rfl

mutual
theorem Ty.ren_eq_subst_var {m n} (ξ : Ren m n) :
    ∀ A : Ty m, A.ren ξ = A.subst ξ.toSubst
  | 𝑢 .. => rfl
  | .pi ⟨_, _⟩ _ => by
    simp only [Ty.ren, Ty.subst, Ty.ren_eq_subst_var, Subst.subst_comp_up]
  | .el t => by simp only [Ty.ren, Ren.toSubst, Ty.subst, Tm.ren_eq_subst_var ξ t]
theorem Tm.ren_eq_subst_var {m n} (ξ : Ren m n) :
    ∀ t : Tm m, t.ren ξ = t.subst ξ.toSubst
  | .u' .. => rfl
  | .var .. => rfl
  | .const .. => rfl
  | .lam ⟨_, _⟩ _ => by
      simp only [Tm.ren, Tm.subst, Ty.ren_eq_subst_var, Tm.ren_eq_subst_var, Subst.subst_comp_up]
  | .app .. => by simp only [Tm.ren, Tm.subst, Tm.ren_eq_subst_var]
  | .pi' .. => by
      simp only [Tm.ren, Tm.subst, Tm.ren_eq_subst_var, Subst.subst_comp_up]
  | .proj .. => by simp only [Tm.ren, Tm.subst, Tm.ren_eq_subst_var]
  | .letE .. => by
      simp only [Tm.ren, Tm.subst, Ty.ren_eq_subst_var, Tm.ren_eq_subst_var, Subst.subst_comp_up]
end

section SubstitutionLemmas

mutual
@[simp]
theorem Ty.subst_id {n} : ∀ A : Ty n, A.subst (Subst.id n) = A
  | 𝑢 .. => rfl
  | .pi ⟨_, _⟩ _ => by simp [Ty.subst, Ty.subst_id]
  | .el .. => by simp only [Ty.subst, Tm.subst_id]
@[simp]
theorem Tm.subst_id {n} : ∀ t : Tm n, t.subst (Subst.id n) = t
  | .u' .. => rfl
  | .var .. => rfl
  | .const .. => rfl
  | .lam ⟨_, _⟩ _ => by simp [Tm.subst, Ty.subst_id, Tm.subst_id]
  | .app .. => by simp [Tm.subst, Tm.subst_id]
  | .pi' .. => by simp [Tm.subst, Tm.subst_id]
  | .proj .. => by simp only [Tm.subst, Tm.subst_id]
  | .letE .. => by simp [Tm.subst, Ty.subst_id, Tm.subst_id]
end

@[simp]
theorem Subst.id_comp {m n} (σ : Subst m n) : (Subst.id m).comp σ = σ := rfl
@[simp]
theorem Subst.comp_id {m n} (σ : Subst m n) : σ.comp (Subst.id n) = σ := by
  funext i; apply Tm.subst_id

theorem Subst.up_eq_cons_ren {m n} (σ : Subst m n) :
    σ.up = .var 0 .: (Tm.ren Ren.shift ∘ σ) := rfl

theorem Subst.cons_comp {l m n} (s : Tm m) (σ : Subst l m) (τ : Subst m n) :
    (s .: σ).comp τ = s.subst τ .: σ.comp τ := by
  funext ⟨i, hi⟩
  cases i <;> rfl

theorem Subst.shift_cons {n m} (s : Tm m) (σ : Subst n m) :
    Subst.shift.comp (s .: σ) = σ := by
  funext ⟨i, hi⟩
  rfl

private theorem Subst.comp_ren_up {l m n} (σ : Subst m n) (ξ : Ren l m) :
    Subst.up (σ ∘ ξ) = σ.up ∘ ξ.up := by
  funext ⟨i, hi⟩
  cases i <;> rfl

mutual
private theorem Ty.ren_subst {l m n} (ξ : Ren l m) (σ : Subst m n) :
    (A : Ty l) → (A.ren ξ).subst σ = A.subst (σ ∘ ξ)
  | 𝑢 .. => rfl
  | .pi ⟨_, _⟩ _ => by simp only [Ty.ren, Ty.subst, Ty.ren_subst, Subst.comp_ren_up]
  | .el .. => by simp only [Ty.ren, Ty.subst, Tm.ren_subst]
private theorem Tm.ren_subst {l m n} (ξ : Ren l m) (σ : Subst m n) :
    ∀ t : Tm l, (t.ren ξ).subst σ = t.subst (σ ∘ ξ)
  | .u' .. => rfl
  | .var .. => rfl
  | .const .. => rfl
  | .lam ⟨_, _⟩ _ => by simp only [Tm.ren, Tm.subst, Ty.ren_subst, Tm.ren_subst, Subst.comp_ren_up]
  | .app .. => by simp only [Tm.ren, Tm.subst, Tm.ren_subst]
  | .pi' .. => by simp only [Tm.ren, Tm.subst, Tm.ren_subst, Subst.comp_ren_up]
  | .proj .. => by simp only [Tm.ren, Tm.subst, Tm.ren_subst]
  | .letE .. => by simp only [Tm.ren, Tm.subst, Ty.ren_subst, Tm.ren_subst, Subst.comp_ren_up]
end

private theorem Subst.ren_comp_up {l m n} (σ : Subst l m) (ξ : Ren m n) :
    Subst.up (Tm.ren ξ ∘ σ) = Tm.ren ξ.up ∘ σ.up := by
  funext ⟨i, hi⟩
  cases i with
  | zero => rfl
  | succ _ => simp only [up, cons, Function.comp_apply, ← Tm.comp_ren, Ren.shift_comp]

mutual
private theorem Ty.subst_ren {l m n} (σ : Subst l m) (ξ : Ren m n) :
    ∀ A : Ty l, (A.subst σ).ren ξ = A.subst (Tm.ren ξ ∘ σ)
  | 𝑢 .. => rfl
  | .pi ⟨_, _⟩ _ => by simp only [Ty.subst, Ty.ren, Ty.subst_ren, Subst.ren_comp_up]
  | .el .. => by simp only [Ty.subst, Ty.ren, Tm.subst_ren]
private theorem Tm.subst_ren {l m n} (σ : Subst l m) (ξ : Ren m n) :
    ∀ t : Tm l, (t.subst σ).ren ξ = t.subst (Tm.ren ξ ∘ σ)
  | .u' .. => rfl
  | .var .. => rfl
  | .const .. => rfl
  | .lam ⟨_, _⟩ _ => by simp only [Tm.subst, Tm.ren, Ty.subst_ren, Tm.subst_ren, Subst.ren_comp_up]
  | .app .. => by simp only [Tm.subst, Tm.ren, Tm.subst_ren]
  | .pi' .. => by simp only [Tm.subst, Tm.ren, Tm.subst_ren, Subst.ren_comp_up]
  | .proj .. => by simp only [Tm.subst, Tm.ren, Tm.subst_ren]
  | .letE .. => by simp only [Tm.subst, Tm.ren, Ty.subst_ren, Tm.subst_ren, Subst.ren_comp_up]
end

theorem Subst.shift_up_comm {m n} (σ : Subst m n) :
    shift.comp σ.up = σ.comp shift := by
  funext ⟨i, hi⟩
  simp [shift]
  apply Tm.ren_eq_subst_var


@[simp]
theorem Subst.up_comp {l m n} (σ : Subst l m) (τ : Subst m n) :
    (σ.comp τ).up = σ.up.comp τ.up := by
  funext ⟨i, hi⟩
  cases i with
  | zero => rfl
  | succ i =>
    simp [Subst.up, Subst.cons, Subst.comp, Tm.subst_ren, Tm.ren_subst]
    rfl

mutual
@[simp]
theorem Ty.comp_subst {l m n} (σ : Subst l m) (τ : Subst m n) :
    ∀ A : Ty l, (A.subst σ).subst τ = A.subst (σ.comp τ)
  | 𝑢 .. => rfl
  | .pi ⟨x, a⟩ b => by simp only [Ty.subst, Ty.comp_subst, Subst.up_comp]
  | .el t => by simp only [Ty.subst, Tm.comp_subst]

@[simp]
theorem Tm.comp_subst {l m n} (σ : Subst l m) (τ : Subst m n) :
    ∀ t : Tm l, (t.subst σ).subst τ = t.subst (σ.comp τ)
  | .u' .. => rfl
  | .var .. => rfl
  | .const .. => rfl
  | .lam ⟨_, _⟩ _ => by simp only [Tm.subst, Ty.comp_subst, Tm.comp_subst, Subst.up_comp]
  | .app .. => by simp only [Tm.subst, Tm.comp_subst]
  | .pi' .. => by simp only [Tm.subst, Tm.comp_subst, Subst.up_comp]
  | .proj .. => by simp only [Tm.subst, Tm.comp_subst]
  | .letE .. => by simp only [Tm.subst, Ty.comp_subst, Tm.comp_subst, Subst.up_comp]
end

theorem Subst.comp_assoc {k l m n} (σ : Subst k l) (τ : Subst l m) (ρ : Subst m n) :
    (σ.comp τ).comp ρ = σ.comp (τ.comp ρ) := by
  funext i
  simp only [Subst.comp, Function.comp_apply]
  exact Tm.comp_subst τ ρ (σ i)

end SubstitutionLemmas

-- Substitutions form a category

-- open CategoryTheory

-- structure Subst.Obj where
--   n : Nat

-- instance : Coe Subst.Obj Nat where
--   coe := Subst.Obj.n

-- instance : Category Subst.Obj where
--   id n := Subst.id n
--   Hom m n := Subst m n
--   comp σ τ := Subst.comp σ τ
--   id_comp σ := Subst.id_comp σ
--   comp_id σ := Subst.comp_id σ
--   assoc σ τ ρ := Subst.comp_assoc σ τ ρ

-- def Subst.upFunctor : Subst.Obj ⥤ Subst.Obj where
--   obj n := ⟨n + 1⟩
--   map := Subst.up
--   map_id n := Subst.up_id n
--   map_comp := Subst.up_comp

theorem Ren.toSubst_up {m n} (ξ : Ren m n) :
    Subst.up (Ren.toSubst ξ) = Ren.toSubst (Ren.up ξ) :=
  Subst.subst_comp_up ξ

def Subst.beta {n : Nat} (s : Tm n) : Subst (n + 1) n := s .: Subst.id n

@[simp]
theorem Subst.shift_beta {n} (s : Tm n) :
    shift.comp (beta s) = id n :=
  rfl

@[simp]
theorem Ty.shift_beta {n} (A : Ty n) (s : Tm n) :
    (A.subst Subst.shift).subst (Subst.beta s) = A := by
  rw [Ty.comp_subst, Subst.shift_beta, Ty.subst_id]

@[simp]
theorem Tm.shift_beta {n} (t : Tm n) (s : Tm n) :
    (t.subst Subst.shift).subst (Subst.beta s) = t := by
  rw [Tm.comp_subst, Subst.shift_beta, Tm.subst_id]

@[simp]
theorem Tm.var_zero_beta {n} (s : Tm n) : (Tm.var 0).subst (Subst.beta s) = s := rfl

@[simp]
theorem Tm.var_succ_beta {n} (i : Idx n) (s : Tm n) :
    (Tm.var i.succ).subst (Subst.beta s) = Tm.var i := rfl

theorem Subst.beta_up_zero {n} (s : Tm n) : (beta s).up 0 = Tm.var 0 := rfl

theorem Subst.beta_up_one {n} (s : Tm n) : (beta s).up 1 = s.subst shift := by
  simp only [up, beta, cons, Function.comp_apply]
  exact Tm.ren_eq_subst_var Ren.shift s

theorem Subst.beta_up_succ_succ {n} (s : Tm n) (i : Idx n) :
    (beta s).up i.succ.succ = Tm.var i.succ := rfl

theorem Subst.beta_comp_shift {n} (s : Tm n) : beta s ∘ Ren.shift = id n := by
  funext i; rfl

theorem Subst.cons_id_comp_shift {n} (s : Tm n) :
    (s .: Tm.var) ∘ Ren.shift = Tm.var := by
  funext i; rfl

theorem Subst.beta_comp_up {m n} (a : Tm m) (σ : Subst m n) :
    (Subst.beta a).comp σ = σ.up.comp (Subst.beta (a.subst σ)) := by
  ext ⟨i, hi⟩
  cases i with
  | zero => rfl
  | succ j =>
    simp only [comp, beta, cons, id, up, Function.comp_apply, Tm.ren_subst, cons_id_comp_shift]
    exact (Tm.subst_id (σ ⟨j, by omega⟩)).symm

theorem Ty.beta_comp_up {m n} (A : Ty (m + 1)) (a : Tm m) (σ : Subst m n) :
    (A.subst (Subst.beta a)).subst σ = (A.subst σ.up).subst (Subst.beta (a.subst σ)) := by
  rw [Ty.comp_subst, Ty.comp_subst, Subst.beta_comp_up]

theorem Tm.beta_comp_up {m n} (t : Tm (m + 1)) (a : Tm m) (σ : Subst m n) :
    (t.subst (Subst.beta a)).subst σ = (t.subst σ.up).subst (Subst.beta (a.subst σ)) := by
  rw [comp_subst, comp_subst, Subst.beta_comp_up]

theorem Subst.beta_comp_beta {n} (a : Tm (n + 1)) (b : Tm n) :
    (beta a).comp (beta b) = (a.subst (beta b)) .: b .: id n := by
  funext ⟨i, hi⟩
  cases i <;> rfl

theorem Subst.beta_up_comp_beta {n} (a : Tm n) (b : Tm n) :
    (beta a).up.comp (beta b) = b .: a .: id n := by
  ext ⟨i, hi⟩
  cases i with
  | zero => rfl
  | succ j =>
    cases j with
    | zero =>
      simp only [Subst.comp, Function.comp_apply, Subst.up, Subst.cons]
      rw [Tm.ren_eq_subst_var]
      exact Tm.shift_beta a b
    | succ k => rfl

theorem Subst.beta_up_comp_beta_up {n} (a : Tm (n + 1)) (b : Tm n) :
    (beta a).up.comp (beta b).up = ((beta a).comp (beta b)).up := by
  rw [← Subst.up_comp]

theorem Subst.beta_up_comp_up {m n} (a : Tm m) (σ : Subst m n) :
    (beta a).up.comp σ.up = σ.up.up.comp (beta (a.subst σ)).up := by
  rw [← up_comp, ← up_comp, beta_comp_up]

theorem Ty.beta_comp_beta {n} (A : Ty (n + 2)) (a : Tm (n + 1)) (b : Tm n) :
    (A.subst (Subst.beta a)).subst (Subst.beta b) =
    A.subst ((Subst.beta a).comp (Subst.beta b)) := by
  rw [Ty.comp_subst]

theorem Tm.beta_comp_beta {n} (t : Tm (n + 2)) (a : Tm (n + 1)) (b : Tm n) :
    (t.subst (Subst.beta a)).subst (Subst.beta b) =
    t.subst ((Subst.beta a).comp (Subst.beta b)) := by
  rw [Tm.comp_subst]

theorem Subst.cons_shift_comp {m n} (s : Tm n) (σ : Subst m n) :
    shift.comp (s .: σ) = σ := shift_cons s σ

prefix:50 "↑" => Ty.subst Subst.shift
prefix:50 "↑" => Tm.subst Subst.shift

abbrev Tm.weaken {n} : Tm n → Tm (n + 1) := Tm.subst Subst.shift
abbrev Ty.weaken {n} : Ty n → Ty (n + 1) := Ty.subst Subst.shift

abbrev Tm.subst1 {n} : Tm n → Tm (n + 1) → Tm n := Tm.subst ∘ Subst.beta
abbrev Ty.subst1 {n} : Tm n → Ty (n + 1) → Ty n := Ty.subst ∘ Subst.beta

instance {n} : GetElem (Tm (n + 1)) (Tm n) (Tm n) fun _ _ => True where
  getElem t i _ := Tm.subst1 i t

instance {n} : GetElem (Ty (n + 1)) (Tm n) (Ty n) fun _ _ => True where
  getElem t i _ := Ty.subst1 i t

def Ren.upN {m n : Nat} : ∀ k, Ren m n → Ren (m + k) (n + k)
  | 0 => _root_.id
  | k + 1 => up ∘ upN k

def Subst.upN {m n : Nat} : ∀ k, Subst m n → Subst (m + k) (n + k)
  | 0 => _root_.id
  | k + 1 => up ∘ upN k

@[simp] theorem Ren.upN_zero {m n : Nat} (ξ : Ren m n) : Ren.upN 0 ξ = ξ := rfl
@[simp] theorem Ren.upN_succ {m n : Nat} (k : Nat) (ξ : Ren m n) : Ren.upN (k + 1) ξ = (Ren.upN k ξ).up := rfl
@[simp] theorem Subst.upN_zero {m n : Nat} (σ : Subst m n) : Subst.upN 0 σ = σ := rfl
@[simp] theorem Subst.upN_succ {m n : Nat} (k : Nat) (σ : Subst m n) : Subst.upN (k + 1) σ = (Subst.upN k σ).up := rfl

@[simp]
theorem Ren.id_upN {n : Nat} : ∀ k, (Ren.id n).upN k = Ren.id (n + k)
  | 0 => rfl
  | k + 1 => by simp [Ren.id_upN]; rfl

@[simp]
theorem Subst.id_upN {n : Nat} : ∀ k, (Subst.id n).upN k = Subst.id (n + k)
  | 0 => rfl
  | k + 1 => by simp [Subst.id_upN]; rfl

theorem Ren.comp_upN {l m n : Nat} (ξ : Ren l m) (ζ : Ren m n) :
    ∀ k, (ξ.comp ζ).upN k = (ξ.upN k).comp (ζ.upN k)
  | 0 => rfl
  | k + 1 => by simp [Ren.comp_upN, Ren.up_comp]

theorem Subst.comp_upN {l m n : Nat} (σ : Subst l m) (τ : Subst m n) :
    ∀ k, (σ.comp τ).upN k = (σ.upN k).comp (τ.upN k)
  | 0 => rfl
  | k + 1 => by simp [Subst.comp_upN]

theorem Subst.shift_upN_beta {n : Nat} (s : Tm n) :
    ∀ k, (Subst.shift.upN k).comp ((Subst.beta s).upN k) = (Subst.id n).upN k
  | 0 => Subst.shift_beta s
  | k + 1 => by
      simp only [Subst.upN_succ, ← Subst.up_comp]
      congr 1
      exact Subst.shift_upN_beta s k

private def Ren.shiftN {a} : (s : Nat) → Ren a (a + s)
  | 0 => Ren.id a
  | s + 1 => Ren.comp (Ren.shiftN s) Ren.shift

private def Idx.shiftAfter (n k s : Nat) : Ren n (n + s) :=
  match k with
  | 0 => Ren.shiftN s
  | k + 1 => match n with
    | 0 => Ren.shiftN s
    | n + 1 => Nat.add_right_comm n 1 s ▸ Ren.up (Idx.shiftAfter n k s)

def Ty.shiftAfter {n : Nat} (k s : Nat) : Ty n → Ty (n + s) :=
  Ty.ren (Idx.shiftAfter n k s)

def Tm.shiftAfter {n : Nat} (k s : Nat) : Tm n → Tm (n + s) :=
  Tm.ren (Idx.shiftAfter n k s)

abbrev Ty.shift {n : Nat} : ∀ s, Ty n → Ty (n + s) := Ty.shiftAfter 0
abbrev Tm.shift {n : Nat} : ∀ s, Tm n → Tm (n + s) := Tm.shiftAfter 0

private unsafe def Tm.wkClosed_impl {n : Nat} : Tm 0 → Tm n := unsafeCast
private unsafe def Ty.wkClosed_impl {n : Nat} : Ty 0 → Ty n := unsafeCast
@[implemented_by Tm.wkClosed_impl]
def Tm.wkClosed {n : Nat} (t : Tm 0) : Tm n := Nat.zero_add n ▸ t.shift n
@[implemented_by Ty.wkClosed_impl]
def Ty.wkClosed {n : Nat} (t : Ty 0) : Ty n := Nat.zero_add n ▸ t.shift n

@[simp]
private theorem Ren.shiftN_zero {a} : Ren.shiftN 0 = Ren.id a := rfl

@[simp]
private theorem Ren.shiftN_one {a} : Ren.shiftN 1 = (Ren.shift : Ren a (a + 1)) := by
  simp [Ren.shiftN, Ren.id_comp]

private theorem Ren.shiftN_succ {a} (s : Nat) :
    (Ren.shiftN (s + 1) : Ren a (a + s + 1)) = Ren.comp (Ren.shiftN s) Ren.shift := rfl

def Subst.shiftN {n} : (s : Nat) → Subst n (n + s)
  | 0 => Subst.id n
  | s + 1 => Subst.comp (Subst.shiftN s) Subst.shift

@[simp]
theorem Subst.shiftN_zero {n} : Subst.shiftN 0 = Subst.id n := rfl

@[simp]
theorem Subst.shiftN_one {n} : Subst.shiftN 1 = (Subst.shift : Subst n (n + 1)) := by
  simp only [Subst.shiftN, Subst.id_comp]

theorem Subst.shiftN_succ {n} (s : Nat) :
    (Subst.shiftN (s + 1) : Subst n (n + s + 1)) = Subst.comp (Subst.shiftN s) Subst.shift := rfl

end Qdt
