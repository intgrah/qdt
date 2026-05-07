module

public import Incremental.Basic
public import Incremental.FreeTheorem

@[expose] public section

namespace Incremental

inductive FM (ℭ : BuildConfig) (q₀ : ℭ.Q) : Type → Type
  | pure {α} (a : α) : FM ℭ q₀ α
  | input {α} (i : ℭ.I) (k : ℭ.V i → FM ℭ q₀ α) : FM ℭ q₀ α
  | fetch {α} (q : ℭ.Q) (hq : ℭ.rel q q₀) (k : ℭ.R q → FM ℭ q₀ α) : FM ℭ q₀ α

namespace FM

variable {ℭ : BuildConfig} {q₀ : ℭ.Q}

def bind {α β : Type} : FM ℭ q₀ α → (α → FM ℭ q₀ β) → FM ℭ q₀ β
  | .pure a, k => k a
  | .input i kt, k => .input i (fun v => bind (kt v) k)
  | .fetch q hq kt, k => .fetch q hq (fun r => bind (kt r) k)

instance : Monad (FM ℭ q₀) where
  pure := .pure
  bind := bind

def evalTree {α : Type} (ι : ∀ i, ℭ.V i)
    (rec : ∀ q, ℭ.rel q q₀ → ℭ.R q) :
    FM ℭ q₀ α → α
  | .pure a => a
  | .input i k => evalTree ι rec (k (ι i))
  | .fetch q hq k => evalTree ι rec (k (rec q hq))

theorem evalTree_bind {α β : Type} (ι : ∀ i, ℭ.V i)
    (rec : ∀ q, ℭ.rel q q₀ → ℭ.R q)
    (ma : FM ℭ q₀ α) (ka : α → FM ℭ q₀ β) :
    evalTree ι rec (bind ma ka) = evalTree ι rec (ka (evalTree ι rec ma)) := by
  induction ma with
  | pure a => rfl
  | input i kt ih =>
    show evalTree ι rec (bind (kt (ι i)) ka) =
         evalTree ι rec (ka (evalTree ι rec (kt (ι i))))
    exact ih (ι i)
  | fetch q hq kt ih =>
    show evalTree ι rec (bind (kt (rec q hq)) ka) =
         evalTree ι rec (ka (evalTree ι rec (kt (rec q hq))))
    exact ih (rec q hq)

def pureInput (i : ℭ.I) : FM ℭ q₀ (ℭ.V i) := .input i .pure

def pureFetch (q : ℭ.Q) (hq : ℭ.rel q q₀) : FM ℭ q₀ (ℭ.R q) :=
  .fetch q hq .pure

def evalTrace_inputs {α : Type} (ι : ∀ i, ℭ.V i)
    (rec : ∀ q, ℭ.rel q q₀ → ℭ.R q) :
    FM ℭ q₀ α → List ((i : ℭ.I) × ℭ.V i)
  | .pure _ => []
  | .input i k => ⟨i, ι i⟩ :: evalTrace_inputs ι rec (k (ι i))
  | .fetch q hq k => evalTrace_inputs ι rec (k (rec q hq))

structure DepTrace (q₀ : ℭ.Q) where
  q : ℭ.Q
  hq : ℭ.rel q q₀
  val : ℭ.R q

def evalTrace_deps {α : Type} (ι : ∀ i, ℭ.V i)
    (rec : ∀ q, ℭ.rel q q₀ → ℭ.R q) :
    FM ℭ q₀ α → List (DepTrace q₀)
  | .pure _ => []
  | .input i k => evalTrace_deps ι rec (k (ι i))
  | .fetch q hq k => ⟨q, hq, rec q hq⟩ :: evalTrace_deps ι rec (k (rec q hq))

theorem evalTrace_inputs_bind {α β : Type} (ι : ∀ i, ℭ.V i)
    (rec : ∀ q, ℭ.rel q q₀ → ℭ.R q)
    (ma : FM ℭ q₀ α) (ka : α → FM ℭ q₀ β) :
    evalTrace_inputs ι rec (bind ma ka) =
      evalTrace_inputs ι rec ma ++ evalTrace_inputs ι rec (ka (evalTree ι rec ma)) := by
  induction ma with
  | pure a => simp [bind, evalTrace_inputs, evalTree]
  | input i kt ih =>
    simp [bind, evalTrace_inputs, evalTree]
    exact ih (ι i)
  | fetch q hq kt ih =>
    simp [bind, evalTrace_inputs, evalTree]
    exact ih (rec q hq)

theorem evalTrace_deps_bind {α β : Type} (ι : ∀ i, ℭ.V i)
    (rec : ∀ q, ℭ.rel q q₀ → ℭ.R q)
    (ma : FM ℭ q₀ α) (ka : α → FM ℭ q₀ β) :
    evalTrace_deps ι rec (bind ma ka) =
      evalTrace_deps ι rec ma ++ evalTrace_deps ι rec (ka (evalTree ι rec ma)) := by
  induction ma with
  | pure a => simp [bind, evalTrace_deps, evalTree]
  | input i kt ih =>
    simp [bind, evalTrace_deps, evalTree]
    exact ih (ι i)
  | fetch q hq kt ih =>
    simp [bind, evalTrace_deps, evalTree]
    exact ih (rec q hq)

theorem evalTrace_inputs_value {α : Type} (ι : ∀ i, ℭ.V i)
    (rec : ∀ q, ℭ.rel q q₀ → ℭ.R q) (t : FM ℭ q₀ α) :
    ∀ p ∈ evalTrace_inputs ι rec t, p.2 = ι p.1 := by
  induction t with
  | pure _ => intro p hp; cases hp
  | input i k ih =>
    intro p hp
    cases hp with
    | head => rfl
    | tail _ ht => exact ih (ι i) p ht
  | fetch q hq k ih =>
    intro p hp
    exact ih (rec q hq) p hp

theorem evalTrace_deps_value {α : Type} (ι : ∀ i, ℭ.V i)
    (rec : ∀ q, ℭ.rel q q₀ → ℭ.R q) (t : FM ℭ q₀ α) :
    ∀ p ∈ evalTrace_deps ι rec t, p.2.2 = rec p.1 p.2.1 := by
  induction t with
  | pure _ => intro p hp; cases hp
  | input i k ih =>
    intro p hp
    exact ih (ι i) p hp
  | fetch q hq k ih =>
    intro p hp
    cases hp with
    | head => rfl
    | tail _ ht => exact ih (rec q hq) p ht

theorem evalTree_cross {α : Type} (ι ι' : ∀ i, ℭ.V i)
    (rec rec' : ∀ q, ℭ.rel q q₀ → ℭ.R q) (t : FM ℭ q₀ α)
    (hin : ∀ p ∈ evalTrace_inputs ι rec t, ι' p.1 = p.2)
    (hdep : ∀ p ∈ evalTrace_deps ι rec t, rec' p.1 p.2.1 = p.2.2) :
    evalTree ι rec t = evalTree ι' rec' t := by
  induction t with
  | pure a => rfl
  | input i k ih =>
    have hi_eq : ι' i = ι i := by
      apply hin ⟨i, ι i⟩
      simp [evalTrace_inputs]
    show evalTree ι rec (k (ι i)) = evalTree ι' rec' (k (ι' i))
    rw [hi_eq]
    apply ih (ι i)
    · intro p hp
      apply hin
      simp [evalTrace_inputs, List.mem_cons]
      exact Or.inr hp
    · intro p hp
      apply hdep
      simp [evalTrace_deps]
      exact hp
  | fetch q hq k ih =>
    have hd_eq : rec' q hq = rec q hq := by
      apply hdep ⟨q, hq, rec q hq⟩
      simp [evalTrace_deps]
    show evalTree ι rec (k (rec q hq)) = evalTree ι' rec' (k (rec' q hq))
    rw [hd_eq]
    apply ih (rec q hq)
    · intro p hp
      apply hin
      simp [evalTrace_inputs]
      exact hp
    · intro p hp
      apply hdep
      simp [evalTrace_deps, List.mem_cons]
      exact Or.inr hp

def evalAction (ι : ∀ i, ℭ.V i) (rec : ∀ q, ℭ.rel q q₀ → ℭ.R q) :
    MonadAction (FM ℭ q₀) Id where
  rel R t a := R (evalTree ι rec t) a
  rel_pure {α β R a b} hab := show R (evalTree ι rec (.pure a)) b from hab
  rel_bind {α₁ α₂ β₁ β₂ R S ma mb ka kb} hma hk := by
    show S (evalTree ι rec (bind ma ka)) (kb mb)
    rw [evalTree_bind]
    exact hk _ mb hma

end FM

variable (ℭ : BuildConfig)

def tasksTree (tasks : Tasks Monad ℭ) (q₀ : ℭ.Q) : FM ℭ q₀ (ℭ.R q₀) :=
  tasks q₀ (FM ℭ q₀) FM.pureInput FM.pureFetch

theorem tasksTree_eval (tasks : Tasks Monad ℭ) (q₀ : ℭ.Q)
    (ι : ∀ i, ℭ.V i) (rec : ∀ q, ℭ.rel q q₀ → ℭ.R q) :
    FM.evalTree ι rec (tasksTree ℭ tasks q₀) = tasks q₀ Id ι rec := by
  have h := Task.freeTheorem (tasks q₀) (FM.evalAction ι rec)
    FM.pureInput ι FM.pureFetch rec
    (fun i => show ι i = ι i from rfl)
    (fun q hq => show rec q hq = rec q hq from rfl)
  exact h

theorem tasksTree_eval_compute (tasks : Tasks Monad ℭ) (q₀ : ℭ.Q)
    (ι : ∀ i, ℭ.V i) :
    FM.evalTree ι (fun q _ => compute (inferInstance : Monad Id) tasks ι q) (tasksTree ℭ tasks q₀) =
      compute (inferInstance : Monad Id) tasks ι q₀ := by
  rw [tasksTree_eval]
  conv => rhs; unfold compute

end Incremental
