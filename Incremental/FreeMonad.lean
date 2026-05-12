module

public import Incremental.Basic
public import Incremental.FreeTheorem

@[expose] public section

namespace Incremental

inductive FM (ℭ : BuildConfig) (q₀ : ℭ.Q) (α : Type) : Type
  | pure (a : α) : FM ℭ q₀ α
  | input (i : ℭ.I) (k : ℭ.V i → FM ℭ q₀ α) : FM ℭ q₀ α
  | fetch (q : ℭ.Q) (hq : ℭ.rel q q₀) (k : ℭ.R q → FM ℭ q₀ α) : FM ℭ q₀ α

namespace FM

variable {ℭ : BuildConfig} {q₀ : ℭ.Q}

def bind {α β : Type} : FM ℭ q₀ α → (α → FM ℭ q₀ β) → FM ℭ q₀ β
  | pure a, k => k a
  | input i kt, k => input i (fun v => bind (kt v) k)
  | fetch q hq kt, k => fetch q hq (fun r => bind (kt r) k)

instance : Monad (FM ℭ q₀) where
  pure := pure
  bind := bind

def evalTree {α : Type} (ι : ∀ i, ℭ.V i) (rec : ∀ q, ℭ.R q) :
    FM ℭ q₀ α → α
  | pure a => a
  | input i k => evalTree ι rec (k (ι i))
  | fetch q _ k => evalTree ι rec (k (rec q))

theorem evalTree_bind {α β : Type} (ι : ∀ i, ℭ.V i) (rec : ∀ q, ℭ.R q)
    (ma : FM ℭ q₀ α) (ka : α → FM ℭ q₀ β) :
    evalTree ι rec (bind ma ka) = evalTree ι rec (ka (evalTree ι rec ma)) := by
  induction ma with
  | pure a => rfl
  | input i kt ih => exact ih (ι i)
  | fetch q _ kt ih => exact ih (rec q)

def pureInput (i : ℭ.I) : FM ℭ q₀ (ℭ.V i) := input i pure

def pureFetch (q : ℭ.Q) (hq : ℭ.rel q q₀) : FM ℭ q₀ (ℭ.R q) :=
  fetch q hq pure

end FM

structure InputEntry (ℭ : BuildConfig) where
  i : ℭ.I
  v : ℭ.V i

structure DepEntry (ℭ : BuildConfig) (q₀ : ℭ.Q) where
  q : ℭ.Q
  hq : ℭ.rel q q₀
  r : ℭ.R q

namespace FM

variable {ℭ : BuildConfig} {q₀ : ℭ.Q}

def evalTrace_inputs {α : Type} (ι : ∀ i, ℭ.V i) (rec : ∀ q, ℭ.R q) :
    FM ℭ q₀ α → List (InputEntry ℭ)
  | pure _ => []
  | input i k => ⟨i, ι i⟩ :: evalTrace_inputs ι rec (k (ι i))
  | fetch q _ k => evalTrace_inputs ι rec (k (rec q))

def evalTrace_deps {α : Type} (ι : ∀ i, ℭ.V i) (rec : ∀ q, ℭ.R q) :
    FM ℭ q₀ α → List (DepEntry ℭ q₀)
  | pure _ => []
  | input i k => evalTrace_deps ι rec (k (ι i))
  | fetch q hq k => ⟨q, hq, rec q⟩ :: evalTrace_deps ι rec (k (rec q))

theorem evalTrace_inputs_bind {α β : Type} (ι : ∀ i, ℭ.V i) (rec : ∀ q, ℭ.R q)
    (ma : FM ℭ q₀ α) (ka : α → FM ℭ q₀ β) :
    evalTrace_inputs ι rec (bind ma ka) =
      evalTrace_inputs ι rec ma ++ evalTrace_inputs ι rec (ka (evalTree ι rec ma)) := by
  induction ma with
  | pure a => rfl
  | input i kt ih => exact congrArg _ (ih (ι i))
  | fetch q _ kt ih => exact ih (rec q)

theorem evalTrace_deps_bind {α β : Type} (ι : ∀ i, ℭ.V i) (rec : ∀ q, ℭ.R q)
    (ma : FM ℭ q₀ α) (ka : α → FM ℭ q₀ β) :
    evalTrace_deps ι rec (bind ma ka) =
      evalTrace_deps ι rec ma ++ evalTrace_deps ι rec (ka (evalTree ι rec ma)) := by
  induction ma with
  | pure a => rfl
  | input i kt ih => exact ih (ι i)
  | fetch q hq kt ih => exact congrArg _ (ih (rec q))

theorem evalTrace_deps_value {α : Type} (ι : ∀ i, ℭ.V i)
    (rec : ∀ q, ℭ.R q) (t : FM ℭ q₀ α) :
    ∀ p ∈ evalTrace_deps ι rec t, p.r = rec p.q := by
  induction t with
  | pure _ => nofun
  | input i k ih => exact ih (ι i)
  | fetch q hq k ih => exact fun
    | _, .head _ => rfl
    | p, .tail _ ht => ih (rec q) p ht

theorem evalTree_cross {α : Type} (ι ι' : ∀ i, ℭ.V i)
    (rec rec' : ∀ q, ℭ.R q) (t : FM ℭ q₀ α)
    (hin : ∀ p ∈ evalTrace_inputs ι rec t, ι' p.i = p.v)
    (hdep : ∀ p ∈ evalTrace_deps ι rec t, rec' p.q = p.r) :
    evalTree ι rec t = evalTree ι' rec' t := by
  induction t with
  | pure a => rfl
  | input i k ih =>
    show evalTree ι rec (k (ι i)) = evalTree ι' rec' (k (ι' i))
    have hi_eq : ι' i = ι i := hin ⟨i, ι i⟩ (.head _)
    rw [hi_eq]
    exact ih (ι i) (fun p hp => hin p (.tail _ hp)) hdep
  | fetch q hq k ih =>
    show evalTree ι rec (k (rec q)) = evalTree ι' rec' (k (rec' q))
    have hd_eq : rec' q = rec q := hdep ⟨q, hq, rec q⟩ (.head _)
    rw [hd_eq]
    exact ih (rec q) hin (fun p hp => hdep p (.tail _ hp))

def evalAction (ι : ∀ i, ℭ.V i) (rec : ∀ q, ℭ.R q) :
    Task.Monad.Action (FM ℭ q₀) Id where
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
    (ι : ∀ i, ℭ.V i) (rec : ∀ q, ℭ.R q) :
    FM.evalTree ι rec (tasksTree ℭ tasks q₀) =
      tasks q₀ Id ι (fun q _ => rec q) :=
  Task.Monad.freeTheorem (tasks q₀) (FM.evalAction ι rec)
    FM.pureInput ι FM.pureFetch (fun q _ => rec q)
    (fun _ => rfl) (fun _ _ => rfl)

theorem tasksTree_eval_compute (tasks : Tasks Monad ℭ) (q₀ : ℭ.Q)
    (ι : ∀ i, ℭ.V i) :
    FM.evalTree ι (compute (inferInstance : Monad Id) tasks ι) (tasksTree ℭ tasks q₀) =
      compute (inferInstance : Monad Id) tasks ι q₀ := by
  rw [tasksTree_eval]
  conv => rhs; unfold compute

end Incremental
