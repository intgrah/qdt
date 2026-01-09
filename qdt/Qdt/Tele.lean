namespace Qdt

universe u v w

inductive Tele (T : Nat → Type u) (a : Nat) : Nat → Type u
  | nil : Tele T a a
  | snoc {b} : Tele T a b → T b → Tele T a (b + 1)

namespace Tele

theorem le
    {T : Nat → Type u}
    {a b : Nat}
    (tele : Tele T a b) :
    a ≤ b := by
  induction tele with
  | nil => exact Nat.le_refl a
  | snoc ts t ih => exact Nat.le_trans ih (Nat.le_succ _)

def append
    {T : Nat → Type u}
    {a b c : Nat}
    (tele₁ : Tele T a b)
    (tele₂ : Tele T b c) :
    Tele T a c :=
  match tele₂ with
  | nil => tele₁
  | snoc ts t => tele₁.append ts |>.snoc t

instance {T : Nat → Type u} {a b c} : HAppend (Tele T a b) (Tele T b c) (Tele T a c) where
  hAppend := append

@[simp]
theorem append_snoc
    {T : Nat → Type u}
    {a b c : Nat}
    (tele₁ : Tele T a b)
    (tele₂ : Tele T b c)
    (t : T c) :
    tele₁ ++ (tele₂.snoc t) = (tele₁ ++ tele₂).snoc t :=
  rfl

@[simp]
theorem append_nil
    {T : Nat → Type u}
    {a b : Nat}
    (tele : Tele T a b) :
    tele.append nil = tele :=
  rfl

@[simp]
theorem nil_append
    {T : Nat → Type u}
    {a b : Nat}
    (tele : Tele T a b) :
    nil.append tele = tele := by
  induction tele with
  | nil => rfl
  | snoc ts t ih => rw [append, ih]

theorem append_assoc
    {T : Nat → Type u}
    {a b c d : Nat}
    (tele₁ : Tele T a b)
    (tele₂ : Tele T b c)
    (tele₃ : Tele T c d) :
    (tele₁ ++ tele₂) ++ tele₃ = tele₁ ++ (tele₂ ++ tele₃) := by
  induction tele₃ with
  | nil => rfl
  | snoc ts t ih => simp only [append_snoc, ih]

def any
    {T : Nat → Type u}
    {a b : Nat}
    (f : ∀ {n}, T n → Bool) :
    Tele T a b →
    Bool
  | nil => false
  | snoc ts t => f t || ts.any f

@[specialize]
def dmap
    {T : Nat → Type u}
    {U : Nat → Type v}
    {a b : Nat}
    (s : Nat)
    (f : ∀ {n}, T n → U (n + s)) :
    Tele T a b →
    Tele U (a + s) (b + s)
  | nil => nil
  | snoc ts t => Nat.succ_add _ s ▸ (ts.dmap s f).snoc (f t)

def map
    {T : Nat → Type u}
    {U : Nat → Type v}
    {a b : Nat} :
    (∀ {n}, T n → U n) →
    Tele T a b →
    Tele U a b :=
  dmap 0

@[specialize]
def mapM
    {m : Type v → Type w}
    [Monad m]
    {T : Nat → Type u}
    {U : Nat → Type v}
    {a b : Nat}
    (f : ∀ {n}, T n → m (U n)) :
    Tele T a b →
    m (Tele U a b)
  | nil => return nil
  | snoc ts t => return (← ts.mapM f).snoc (← f t)

theorem dmap_snoc
    {T : Nat → Type u}
    {U : Nat → Type v}
    {a b : Nat}
    (s : Nat)
    (f : ∀ {n}, T n → U (n + s))
    (ts : Tele T a b)
    (t : T b) :
    dmap s f (ts.snoc t) = Nat.succ_add b s ▸ (dmap s f ts).snoc (f t) :=
  rfl

instance {T : Nat → Type u} {a b} : HAppend (Tele T a b) (T b) (Tele T a (b + 1)) where
  hAppend := snoc

@[app_unexpander snoc]
def snoc.unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $ts $t) => `($ts ++ $t)
  | _ => throw ()

end Tele
end Qdt
