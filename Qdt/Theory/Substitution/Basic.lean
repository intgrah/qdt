module

public import Qdt.Theory.Substitution.Ren

@[expose] public section

namespace Qdt

def Subst (a b : Nat) := Idx a → Tm b
def Subst.id (a : Nat) : Subst a a := Tm.var
def Subst.shift {a} : Subst a (a + 1) := Subst.id (a + 1) ∘ Ren.shift
def Subst.cons {a b} (s : Tm b) (σ : Subst a b) : Subst (a + 1) b
  | ⟨0, _⟩ => s
  | ⟨i + 1, h⟩ => σ ⟨i, by omega⟩

infixr:67 " .: " => Subst.cons

@[ext]
theorem Subst.ext {a b : Nat} {σ τ : Subst a b} : (∀ i, σ i = τ i) → σ = τ := funext

def Subst.up {m n} (σ : Subst m n) : Subst (m + 1) (n + 1) :=
  Subst.id (n + 1) 0 .: Tm.ren Ren.shift ∘ σ

@[simp]
theorem Subst.up_id (n : Nat) : (Subst.id n).up = Subst.id (n + 1) := by
  funext ⟨i, _⟩; cases i <;> rfl

mutual

def Ty.subst {m n : Nat} (σ : Subst m n) : Ty m → Ty n
  | .u i => .u i
  | .pi x a b => .pi x (a.subst σ) (b.subst σ.up)
  | .el t => .el (t.subst σ)

def Tm.subst {m n : Nat} (σ : Subst m n) : Tm m → Tm n
  | .u' i => .u' i
  | .var i => σ i
  | .const name us => .const name us
  | .lam x a body => .lam x (a.subst σ) (body.subst σ.up)
  | .app f a => .app (f.subst σ) (a.subst σ)
  | .pi' x a b => .pi' x (a.subst σ) (b.subst σ.up)
  | .proj i t => .proj i (t.subst σ)
  | .letE x ty t body => .letE x (ty.subst σ) (t.subst σ) (body.subst σ.up)

end

@[simp]
theorem Tm.subst_var {m n : Nat} (σ : Subst m n) (i : Idx m) :
    Tm.subst σ (.var i) = σ i := rfl

def Subst.comp {l m n : Nat} (σ : Subst l m) (τ : Subst m n) : Subst l n := Tm.subst τ ∘ σ

abbrev Ren.toSubst {m n} (ξ : Ren m n) : Subst m n := fun i => Tm.var (ξ i)

theorem Subst.subst_comp_up {m n} (ξ : Ren m n) :
    ξ.toSubst.up = ξ.up.toSubst := by
  funext ⟨i, _⟩; cases i <;> rfl

mutual

theorem Ty.ren_eq_subst_var {m n} (ξ : Ren m n) :
    ∀ A : Ty m, A.ren ξ = A.subst ξ.toSubst
  | .u .. => rfl
  | .pi _ _ _ => by
    simp only [Ty.ren, Ty.subst, Ty.ren_eq_subst_var, Subst.subst_comp_up]
  | .el t => by simp only [Ty.ren, Ty.subst, Tm.ren_eq_subst_var ξ t]

theorem Tm.ren_eq_subst_var {m n} (ξ : Ren m n) :
    ∀ t : Tm m, t.ren ξ = t.subst ξ.toSubst
  | .u' .. => rfl
  | .var _ => rfl
  | .const .. => rfl
  | .lam _ _ _ => by
      simp only [Tm.ren, Tm.subst, Ty.ren_eq_subst_var, Tm.ren_eq_subst_var, Subst.subst_comp_up]
  | .app .. => by simp only [Tm.ren, Tm.subst, Tm.ren_eq_subst_var]
  | .pi' _ _ _ => by
      simp only [Tm.ren, Tm.subst, Tm.ren_eq_subst_var, Subst.subst_comp_up]
  | .proj .. => by simp only [Tm.ren, Tm.subst, Tm.ren_eq_subst_var]
  | .letE .. => by
      simp only [Tm.ren, Tm.subst, Ty.ren_eq_subst_var, Tm.ren_eq_subst_var, Subst.subst_comp_up]

end

section SubstitutionLemmas

mutual

@[simp]
theorem Ty.subst_id {n} : ∀ A : Ty n, A.subst (Subst.id n) = A
  | .u .. => rfl
  | .pi .. => by simp only [Ty.subst, Ty.subst_id, Subst.up_id]
  | .el .. => by simp only [Ty.subst, Tm.subst_id]

@[simp]
theorem Tm.subst_id {n} : ∀ t : Tm n, t.subst (Subst.id n) = t
  | .u' .. => rfl
  | .var _ => rfl
  | .const .. => rfl
  | .lam .. => by simp only [Tm.subst, Ty.subst_id, Tm.subst_id, Subst.up_id]
  | .app .. => by simp only [Tm.subst, Tm.subst_id]
  | .pi' .. => by simp only [Tm.subst, Tm.subst_id, Subst.up_id]
  | .proj .. => by simp only [Tm.subst, Tm.subst_id]
  | .letE .. => by simp only [Tm.subst, Ty.subst_id, Tm.subst_id, Subst.up_id]

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
  funext ⟨i, _⟩
  cases i <;> rfl

theorem Subst.shift_cons {n m} (s : Tm m) (σ : Subst n m) :
    Subst.shift.comp (s .: σ) = σ := rfl

theorem Subst.comp_ren_up {l m n} (σ : Subst m n) (ξ : Ren l m) :
    Subst.up (σ ∘ ξ) = σ.up ∘ ξ.up := by
  funext ⟨i, _⟩
  cases i <;> rfl

mutual

theorem Ty.ren_subst {l m n} (ξ : Ren l m) (σ : Subst m n) :
    (A : Ty l) → (A.ren ξ).subst σ = A.subst (σ ∘ ξ)
  | .u .. => rfl
  | .pi _ _ _ => by simp only [Ty.ren, Ty.subst, Ty.ren_subst, Subst.comp_ren_up]
  | .el .. => by simp only [Ty.ren, Ty.subst, Tm.ren_subst]

theorem Tm.ren_subst {l m n} (ξ : Ren l m) (σ : Subst m n) :
    ∀ t : Tm l, (t.ren ξ).subst σ = t.subst (σ ∘ ξ)
  | .u' .. => rfl
  | .var _ => rfl
  | .const .. => rfl
  | .lam _ _ _ => by simp only [Tm.ren, Tm.subst, Tm.ren_subst, Ty.ren_subst, Subst.comp_ren_up]
  | .app .. => by simp only [Tm.ren, Tm.subst, Tm.ren_subst]
  | .pi' _ _ _ => by simp only [Tm.ren, Tm.subst, Tm.ren_subst, Subst.comp_ren_up]
  | .proj .. => by simp only [Tm.ren, Tm.subst, Tm.ren_subst]
  | .letE .. => by simp only [Tm.ren, Tm.subst, Tm.ren_subst, Ty.ren_subst, Subst.comp_ren_up]

end

theorem Subst.ren_comp_up {l m n} (σ : Subst l m) (ξ : Ren m n) :
    Subst.up (Tm.ren ξ ∘ σ) = Tm.ren ξ.up ∘ σ.up := by
  funext ⟨i, _⟩
  cases i with
  | zero => rfl
  | succ _ => simp only [up, cons, Function.comp_apply, ← Tm.comp_ren, Ren.shift_comp]

mutual

theorem Ty.subst_ren {l m n} (σ : Subst l m) (ξ : Ren m n) :
    ∀ A : Ty l, (A.subst σ).ren ξ = A.subst (Tm.ren ξ ∘ σ)
  | .u .. => rfl
  | .pi _ _ _ => by simp only [Ty.subst, Ty.ren, Ty.subst_ren, Subst.ren_comp_up]
  | .el .. => by simp only [Ty.subst, Ty.ren, Tm.subst_ren]

theorem Tm.subst_ren {l m n} (σ : Subst l m) (ξ : Ren m n) :
    ∀ t : Tm l, (t.subst σ).ren ξ = t.subst (Tm.ren ξ ∘ σ)
  | .u' .. => rfl
  | .var _ => rfl
  | .const .. => rfl
  | .lam _ _ _ => by simp only [Tm.subst, Tm.ren, Ty.subst_ren, Tm.subst_ren, Subst.ren_comp_up]
  | .app .. => by simp only [Tm.subst, Tm.ren, Tm.subst_ren]
  | .pi' _ _ _ => by simp only [Tm.subst, Tm.ren, Tm.subst_ren, Subst.ren_comp_up]
  | .proj .. => by simp only [Tm.subst, Tm.ren, Tm.subst_ren]
  | .letE .. => by simp only [Tm.subst, Tm.ren, Ty.subst_ren, Tm.subst_ren, Subst.ren_comp_up]

end

@[simp]
theorem Subst.up_comp {l m n} (σ : Subst l m) (τ : Subst m n) :
    (σ.comp τ).up = σ.up.comp τ.up := by
  funext ⟨i, _⟩
  cases i with
  | zero => rfl
  | succ _ =>
    simp only [Subst.up, Subst.cons, Subst.comp, Function.comp_apply,
      Tm.subst_ren, Tm.ren_subst]
    rfl

mutual

@[simp]
theorem Ty.comp_subst {l m n} (σ : Subst l m) (τ : Subst m n) :
    ∀ A : Ty l, (A.subst σ).subst τ = A.subst (σ.comp τ)
  | .u .. => rfl
  | .pi _ _ _ => by simp only [Ty.subst, Ty.comp_subst, Subst.up_comp]
  | .el .. => by simp only [Ty.subst, Tm.comp_subst]

@[simp]
theorem Tm.comp_subst {l m n} (σ : Subst l m) (τ : Subst m n) :
    ∀ t : Tm l, (t.subst σ).subst τ = t.subst (σ.comp τ)
  | .u' .. => rfl
  | .var .. => rfl
  | .const .. => rfl
  | .lam _ _ _ => by simp only [Tm.subst, Ty.comp_subst, Tm.comp_subst, Subst.up_comp]
  | .app .. => by simp only [Tm.subst, Tm.comp_subst]
  | .pi' _ _ _ => by simp only [Tm.subst, Tm.comp_subst, Subst.up_comp]
  | .proj .. => by simp only [Tm.subst, Tm.comp_subst]
  | .letE .. => by simp only [Tm.subst, Ty.comp_subst, Tm.comp_subst, Subst.up_comp]

end

theorem Subst.comp_assoc {k l m n} (σ : Subst k l) (τ : Subst l m) (ρ : Subst m n) :
    (σ.comp τ).comp ρ = σ.comp (τ.comp ρ) := by
  funext i
  simp only [Subst.comp, Function.comp_apply]
  exact Tm.comp_subst τ ρ (σ i)

end SubstitutionLemmas

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
theorem Tm.var_zero_beta {n} (s : Tm n) :
    (Tm.var 0).subst (Subst.beta s) = s := rfl

@[simp]
theorem Tm.var_succ_beta {n} (i : Idx n) (s : Tm n) :
    (Tm.var i.succ).subst (Subst.beta s) = Subst.id n i := rfl

theorem Subst.beta_up_zero {n} (s : Tm n) : (beta s).up 0 = Tm.var 0 := rfl

theorem Subst.beta_up_one {n} (s : Tm n) : (beta s).up 1 = s.subst shift :=
  Tm.ren_eq_subst_var Ren.shift s

theorem Subst.beta_up_succ_succ {n} (s : Tm n) (i : Idx n) :
    (beta s).up i.succ.succ = Subst.id (n + 1) i.succ := rfl

theorem Subst.beta_comp_shift {n} (s : Tm n) : beta s ∘ Ren.shift = id n := rfl

theorem Subst.cons_id_comp_shift {n} (s : Tm n) :
    (s .: Subst.id n) ∘ Ren.shift = Subst.id n := rfl

theorem Subst.beta_comp_up {m n} (a : Tm m) (σ : Subst m n) :
    (Subst.beta a).comp σ = σ.up.comp (Subst.beta (a.subst σ)) := by
  ext ⟨i, _⟩
  cases i with
  | zero => rfl
  | succ j =>
    simp only [comp, beta, cons, id, up, Function.comp_apply, Tm.ren_subst]
    exact (Tm.subst_id (σ ⟨j, by omega⟩)).symm

theorem Ty.beta_comp_up {m n} (A : Ty (m + 1)) (a : Tm m) (σ : Subst m n) :
    (A.subst (Subst.beta a)).subst σ = (A.subst σ.up).subst (Subst.beta (a.subst σ)) := by
  rw [Ty.comp_subst, Ty.comp_subst, Subst.beta_comp_up]

theorem Tm.beta_comp_up {m n} (t : Tm (m + 1)) (a : Tm m) (σ : Subst m n) :
    (t.subst (Subst.beta a)).subst σ = (t.subst σ.up).subst (Subst.beta (a.subst σ)) := by
  rw [comp_subst, comp_subst, Subst.beta_comp_up]

theorem Subst.beta_comp_beta {n} (a : Tm (n + 1)) (b : Tm n) :
    (beta a).comp (beta b) = (a.subst (beta b)) .: b .: id n := by
  funext ⟨i, _⟩
  cases i <;> rfl

theorem Subst.beta_up_comp_beta {n} (a : Tm n) (b : Tm n) :
    (beta a).up.comp (beta b) = b .: a .: id n := by
  ext ⟨i, _⟩
  cases i with
  | zero => rfl
  | succ j =>
    cases j with
    | zero =>
      simp only [Subst.comp, Function.comp_apply, Subst.up, Subst.cons]
      rw [Tm.ren_eq_subst_var]
      exact Tm.shift_beta a b
    | succ _ => rfl

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

@[simp]
theorem Ren.upN_zero {m n : Nat} (ξ : Ren m n) : Ren.upN 0 ξ = ξ := rfl

@[simp]
theorem Ren.upN_succ {m n : Nat} (k : Nat) (ξ : Ren m n) :
    Ren.upN (k + 1) ξ = (Ren.upN k ξ).up := rfl

@[simp]
theorem Subst.upN_zero {m n : Nat} (σ : Subst m n) : Subst.upN 0 σ = σ := rfl

@[simp]
theorem Subst.upN_succ {m n : Nat} (k : Nat) (σ : Subst m n) :
    Subst.upN (k + 1) σ = (Subst.upN k σ).up := rfl

@[simp]
theorem Ren.id_upN {n : Nat} : ∀ k, (Ren.id n).upN k = Ren.id (n + k)
  | 0 => rfl
  | k + 1 => by simp only [Ren.upN_succ, Ren.id_upN, Ren.up_id]; rfl

@[simp]
theorem Subst.id_upN {n : Nat} : ∀ k, (Subst.id n).upN k = Subst.id (n + k)
  | 0 => rfl
  | k + 1 => by simp only [Subst.upN_succ, Subst.id_upN, Subst.up_id]; rfl

theorem Ren.comp_upN {l m n : Nat} (ξ : Ren l m) (ζ : Ren m n) :
    ∀ k, (ξ.comp ζ).upN k = (ξ.upN k).comp (ζ.upN k)
  | 0 => rfl
  | k + 1 => by simp only [Ren.upN_succ, Ren.comp_upN, Ren.up_comp]

theorem Subst.comp_upN {l m n : Nat} (σ : Subst l m) (τ : Subst m n) :
    ∀ k, (σ.comp τ).upN k = (σ.upN k).comp (τ.upN k)
  | 0 => rfl
  | k + 1 => by simp only [Subst.upN_succ, Subst.comp_upN, Subst.up_comp]

theorem Subst.shift_upN_beta {n : Nat} (s : Tm n) :
    ∀ k, (Subst.shift.upN k).comp ((Subst.beta s).upN k) = (Subst.id n).upN k
  | 0 => Subst.shift_beta s
  | k + 1 => by
    simp only [Subst.upN_succ, ← Subst.up_comp]
    congr 1
    exact Subst.shift_upN_beta s k

def Ren.shiftN {a} : (s : Nat) → Ren a (a + s)
  | 0 => Ren.id a
  | s + 1 => Ren.comp (Ren.shiftN s) Ren.shift

def Idx.shiftAfter (n k s : Nat) : Ren n (n + s) :=
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

def Subst.ofEmpty {n : Nat} : Subst 0 n := fun i => nomatch i

@[simp]
theorem Subst.ofEmpty_unique {n : Nat} (σ : Subst 0 n) : σ = Subst.ofEmpty := by
  funext i; exact nomatch i

def Subst.fromArgs {n k : Nat} (args : List (Tm n)) (h : args.length = k) :
    Subst k n :=
  fun ⟨i, hi⟩ => args.reverse[i]'(by rw [List.length_reverse, h]; exact hi)

theorem Subst.fromArgs_ren {n m k : Nat} (args : List (Tm n))
    (h : args.length = k) (ξ : Ren n m) (i : Idx k) :
    (Subst.fromArgs args h i).ren ξ
      = Subst.fromArgs (args.map (Tm.ren ξ ·))
          (by rw [List.length_map]; exact h) i := by
  have ⟨i, _⟩ := i
  simp only [Subst.fromArgs, ← List.map_reverse, List.getElem_map]

theorem Tm.ren_apps {n m : Nat} (t : Tm n) (args : List (Tm n)) (ξ : Ren n m) :
    (t.apps args).ren ξ = (t.ren ξ).apps (args.map (Tm.ren ξ ·)) := by
  induction args generalizing t with
  | nil => rfl
  | cons a rest ih => exact ih (t.app a)

unsafe def Tm.wkClosed_impl {n : Nat} : Tm 0 → Tm n := unsafeCast
unsafe def Ty.wkClosed_impl {n : Nat} : Ty 0 → Ty n := unsafeCast

@[implemented_by Tm.wkClosed_impl]
def Tm.wkClosed {n : Nat} (t : Tm 0) : Tm n := t.subst Subst.ofEmpty

@[implemented_by Ty.wkClosed_impl]
def Ty.wkClosed {n : Nat} (t : Ty 0) : Ty n := t.subst Subst.ofEmpty

theorem Tm.wkClosed_subst {n m : Nat} (t : Tm 0) (σ : Subst n m) :
    (Tm.wkClosed t : Tm n).subst σ = (Tm.wkClosed t : Tm m) := by
  rw [Tm.wkClosed, Tm.comp_subst]
  congr 1
  apply Subst.ofEmpty_unique

theorem Ty.wkClosed_subst {n m : Nat} (t : Ty 0) (σ : Subst n m) :
    (Ty.wkClosed t : Ty n).subst σ = (Ty.wkClosed t : Ty m) := by
  rw [Ty.wkClosed, Ty.comp_subst]
  congr 1
  apply Subst.ofEmpty_unique

theorem Tm.wkClosed_ren {n m : Nat} (t : Tm 0) (ξ : Ren n m) :
    (Tm.wkClosed t : Tm n).ren ξ = (Tm.wkClosed t : Tm m) := by
  rw [Tm.ren_eq_subst_var]
  exact Tm.wkClosed_subst t ξ.toSubst

theorem Ty.wkClosed_ren {n m : Nat} (t : Ty 0) (ξ : Ren n m) :
    (Ty.wkClosed t : Ty n).ren ξ = (Ty.wkClosed t : Ty m) := by
  rw [Ty.ren_eq_subst_var]
  exact Ty.wkClosed_subst t ξ.toSubst

theorem Ty.beta_ren_up {n m : Nat} (B : Ty (n + 1)) (a : Tm n) (ξ : Ren n m) :
    (B.subst (Subst.beta a)).ren ξ = (B.ren ξ.up).subst (Subst.beta (a.ren ξ)) :=
  calc (B.subst (Subst.beta a)).ren ξ
    _ = (B.subst (Subst.beta a)).subst ξ.toSubst := Ty.ren_eq_subst_var ξ _
    _ = (B.subst ξ.toSubst.up).subst (Subst.beta (a.subst ξ.toSubst)) :=
      Ty.beta_comp_up B a ξ.toSubst
    _ = (B.subst ξ.up.toSubst).subst (Subst.beta (a.subst ξ.toSubst)) := by
      rw [Subst.subst_comp_up]
    _ = (B.ren ξ.up).subst (Subst.beta (a.subst ξ.toSubst)) := by
      rw [← Ty.ren_eq_subst_var ξ.up B]
    _ = (B.ren ξ.up).subst (Subst.beta (a.ren ξ)) := by
      rw [← Tm.ren_eq_subst_var ξ a]

theorem Tm.beta_ren_up {n m : Nat} (t : Tm (n + 1)) (a : Tm n) (ξ : Ren n m) :
    (t.subst (Subst.beta a)).ren ξ = (t.ren ξ.up).subst (Subst.beta (a.ren ξ)) :=
  calc (t.subst (Subst.beta a)).ren ξ
    _ = (t.subst (Subst.beta a)).subst ξ.toSubst := Tm.ren_eq_subst_var ξ _
    _ = (t.subst ξ.toSubst.up).subst (Subst.beta (a.subst ξ.toSubst)) :=
      Tm.beta_comp_up t a ξ.toSubst
    _ = (t.subst ξ.up.toSubst).subst (Subst.beta (a.subst ξ.toSubst)) := by
      rw [Subst.subst_comp_up]
    _ = (t.ren ξ.up).subst (Subst.beta (a.subst ξ.toSubst)) := by
      rw [← Tm.ren_eq_subst_var ξ.up t]
    _ = (t.ren ξ.up).subst (Subst.beta (a.ren ξ)) := by
      rw [← Tm.ren_eq_subst_var ξ a]

theorem Tm.shift_ren_up {n m : Nat} (t : Tm n) (ξ : Ren n m) :
    (t.subst Subst.shift).ren ξ.up = (t.ren ξ).subst Subst.shift := by
  rw [Tm.ren_eq_subst_var ξ.up, Tm.comp_subst,
      Tm.ren_eq_subst_var ξ, Tm.comp_subst]
  rfl

@[simp]
theorem Ren.shiftN_zero {a} : Ren.shiftN 0 = Ren.id a := rfl

@[simp]
theorem Ren.shiftN_one {a} : Ren.shiftN 1 = (Ren.shift : Ren a (a + 1)) :=
  Ren.id_comp _

theorem Ren.shiftN_succ {a} (s : Nat) :
    (Ren.shiftN (s + 1) : Ren a (a + s + 1)) = Ren.comp (Ren.shiftN s) Ren.shift := rfl

def Subst.shiftN {n} : (s : Nat) → Subst n (n + s)
  | 0 => Subst.id n
  | s + 1 => Subst.comp (Subst.shiftN s) Subst.shift

@[simp]
theorem Subst.shiftN_zero {n} : Subst.shiftN 0 = Subst.id n := rfl

@[simp]
theorem Subst.shiftN_one {n} : Subst.shiftN 1 = (Subst.shift : Subst n (n + 1)) :=
  Subst.id_comp _

theorem Subst.shiftN_succ {n} (s : Nat) :
    (Subst.shiftN (s + 1) : Subst n (n + s + 1)) = Subst.comp (Subst.shiftN s) Subst.shift := rfl

theorem Subst.shift_comp_up {n m : Nat} (σ : Subst n m) :
    Subst.shift.comp σ.up = σ.comp Subst.shift := by
  funext ⟨i, hi⟩
  show Tm.subst σ.up (Subst.shift ⟨i, hi⟩) = Tm.subst Subst.shift (σ ⟨i, hi⟩)
  have h : (Subst.shift : Subst m (m + 1)) = (Ren.shift : Ren m (m + 1)).toSubst := rfl
  rw [h, ← Tm.ren_eq_subst_var]
  rfl

theorem Ty.shift_subst_comm {n m : Nat} (σ : Subst n m) (A : Ty n) :
    (A.subst Subst.shift).subst σ.up = (A.subst σ).subst Subst.shift := by
  rw [Ty.comp_subst, Ty.comp_subst, Subst.shift_comp_up]

theorem Tm.shift_subst_comm {n m : Nat} (σ : Subst n m) (t : Tm n) :
    (t.subst Subst.shift).subst σ.up = (t.subst σ).subst Subst.shift := by
  rw [Tm.comp_subst, Tm.comp_subst, Subst.shift_comp_up]

end Qdt
