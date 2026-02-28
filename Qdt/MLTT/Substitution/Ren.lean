import Qdt.MLTT.Syntax

namespace Qdt

def Ren (a b : Nat) := Idx a → Idx b
def Ren.id (a : Nat) : Ren a a := fun i => i
def Ren.shift {a} : Ren a (a + 1) := Fin.succ
def Ren.comp {l m n : Nat} (ξ : Ren l m) (ζ : Ren m n) : Ren l n := ζ ∘ ξ

def Ren.cons {a b} (j : Idx b) (ξ : Ren a b) : Ren (a + 1) b
  | ⟨0, _⟩ => j
  | ⟨i + 1, h⟩ => ξ ⟨i, by omega⟩

infixr:67 " .: " => Ren.cons

def Ren.up {a b} (ξ : Ren a b) : Ren (a + 1) (b + 1) := 0 .: Ren.shift ∘ ξ

mutual

def Ty.ren {m n : Nat} (ξ : Ren m n) : Ty m → Ty n
  | .u i => .u i
  | .pi ⟨x, a⟩ b => .pi ⟨x, a.ren ξ⟩ (b.ren ξ.up)
  | .el t => .el (t.ren ξ)

def Tm.ren {m n : Nat} (ξ : Ren m n) : Tm m → Tm n
  | .u' i => .u' i
  | .var i => .var (ξ i)
  | .const x us => .const x us
  | .lam ⟨x, a⟩ body => .lam ⟨x, a.ren ξ⟩ (body.ren ξ.up)
  | .app f a => .app (f.ren ξ) (a.ren ξ)
  | .pi' ⟨x, a⟩ b => .pi' ⟨x, a.ren ξ⟩ (b.ren ξ.up)
  | .proj i t => .proj i (t.ren ξ)
  | .letE x ty t body => .letE x (ty.ren ξ) (t.ren ξ) (body.ren ξ.up)

end

section Lemmas

theorem Ren.id_comp {m n} (ξ : Ren m n) : Ren.comp (Ren.id m) ξ = ξ :=
  Function.id_comp ξ

theorem Ren.comp_id {m n}(ξ : Ren m n) : Ren.comp ξ (Ren.id n) = ξ :=
  Function.comp_id ξ

theorem Ren.comp_assoc {k l m n} (ξ : Ren k l) (ζ : Ren l m) (η : Ren m n) :
    (ξ.comp ζ).comp η = ξ.comp (ζ.comp η) := rfl

@[simp]
theorem Ren.up_id (n : Nat) : (Ren.id n).up = Ren.id (n + 1) := by
  funext ⟨i, hi⟩; cases i <;> rfl

@[simp]
theorem Ren.up_comp {l m n : Nat} (ξ : Ren l m) (ζ : Ren m n) :
    (ξ.comp ζ).up = ξ.up.comp ζ.up := by
  funext ⟨i, hi⟩; cases i <;> rfl

mutual

@[simp]
theorem Ty.ren_id {n} : ∀ A : Ty n, A.ren (Ren.id n) = A
  | .u .. => rfl
  | .pi ⟨_, _⟩ _ => by simp [Ty.ren, Ty.ren_id]
  | .el .. => by simp [Ty.ren, Tm.ren_id]

@[simp]
theorem Tm.ren_id {n} : ∀ t : Tm n, t.ren (Ren.id n) = t
  | .u' .. => rfl
  | .var .. => rfl
  | .const .. => rfl
  | .lam ⟨_, _⟩ _ => by simp [Tm.ren, Ty.ren_id, Tm.ren_id]
  | .app .. => by simp only [Tm.ren, Tm.ren_id]
  | .pi' ⟨_, _⟩ _ => by simp [Tm.ren, Tm.ren_id]
  | .proj .. => by simp only [Tm.ren, Tm.ren_id]
  | .letE .. => by simp [Tm.ren, Ty.ren_id, Tm.ren_id]

end

theorem Ren.shift_comp {m n} (ξ : Ren m n) :
    Ren.shift.comp ξ.up = ξ.comp Ren.shift := rfl

mutual

@[simp]
theorem Ty.comp_ren {l m n} (ξ : Ren l m) (ζ : Ren m n) :
    ∀ A : Ty l, A.ren (ξ.comp ζ) = (A.ren ξ).ren ζ
  | .u .. => rfl
  | .pi ⟨_, _⟩ _ => by simp [Ty.ren, Ty.comp_ren]
  | .el .. => by simp only [Ty.ren, Tm.comp_ren]

@[simp]
theorem Tm.comp_ren {l m n} (ξ : Ren l m) (ζ : Ren m n) :
    ∀ t : Tm l, t.ren (ξ.comp ζ) = (t.ren ξ).ren ζ
  | .u' .. => rfl
  | .var .. => rfl
  | .const .. => rfl
  | .lam ⟨_, _⟩ _ => by simp [Tm.ren, Ty.comp_ren, Tm.comp_ren]
  | .app .. => by simp only [Tm.ren, Tm.comp_ren]
  | .pi' ⟨_, _⟩ _ => by simp [Tm.ren, Tm.comp_ren]
  | .proj .. => by simp only [Tm.ren, Tm.comp_ren]
  | .letE .. => by simp [Tm.ren, Ty.comp_ren, Tm.comp_ren]

end

end Lemmas
