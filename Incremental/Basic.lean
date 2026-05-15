module

public import Mathlib.Logic.Function.Basic
public import Std.Data.DHashMap
public import Std.Data.HashMap
public import Std.Data.HashSet

@[expose] public section

namespace Incremental

open Std (DHashMap HashMap HashSet)

universe u v

abbrev Const (α : Type u) (_ : Type v) : Type u := α

instance {α : Type u} : Applicative (Const (List α)) where
  pure _ := []
  seq f x := f ++ x ()

structure BuildConfig : Type 1 where
  I : Type
  V : I → Type
  Q : Type
  R : Q → Type
  rel : Q → Q → Prop
  wf : WellFounded rel

structure QueryDep (ℭ : BuildConfig) (q₀ : ℭ.Q) where
  q : ℭ.Q
  rel : ℭ.rel q q₀

structure QueryDepHash (ℭ : BuildConfig) (q₀ : ℭ.Q) (H : Type)
    extends QueryDep ℭ q₀ where
  hash : H

structure InputDep (I : Type) where
  key : I

structure InputDepHash (I H : Type) extends InputDep I where
  hash : H

structure MonadAction (κ₁ κ₂ : Type → Type) [Monad κ₁] [Monad κ₂] where
  rel {α β : Type} :
    (α → β → Prop) →
    (κ₁ α → κ₂ β → Prop)
  rel_pure {α β : Type} {R : α → β → Prop} {a : α} {b : β} :
    R a b → rel R (pure a) (pure b)
  rel_bind {α₁ α₂ β₁ β₂ : Type}
    {R : α₁ → α₂ → Prop} {S : β₁ → β₂ → Prop}
    {ma : κ₁ α₁} {mb : κ₂ α₂}
    {ka : α₁ → κ₁ β₁} {kb : α₂ → κ₂ β₂} :
    rel R ma mb →
    (∀ a b, R a b → rel S (ka a) (kb b)) →
    rel S (ma >>= ka) (mb >>= kb)

structure Task (ℭ : BuildConfig) (q₀ : ℭ.Q) (α : Type) : Type 1 where
  fn : ∀ (f : Type → Type) [Monad f],
    (∀ i, f (ℭ.V i)) → (∀ q, ℭ.rel q q₀ → f (ℭ.R q)) → f α
  param {κ₁ κ₂ : Type → Type} [Monad κ₁] [Monad κ₂]
    (A : MonadAction κ₁ κ₂)
    {ι₁ : ∀ i, κ₁ (ℭ.V i)} {ι₂ : ∀ i, κ₂ (ℭ.V i)}
    (f₁ : ∀ q, ℭ.rel q q₀ → κ₁ (ℭ.R q))
    (f₂ : ∀ q, ℭ.rel q q₀ → κ₂ (ℭ.R q)) :
    (∀ i, A.rel Eq (ι₁ i) (ι₂ i)) →
    (∀ q hq, A.rel Eq (f₁ q hq) (f₂ q hq)) →
    A.rel Eq (fn κ₁ ι₁ f₁) (fn κ₂ ι₂ f₂)

namespace Task

variable {ℭ : BuildConfig} {q₀ : ℭ.Q}

@[inline] def pure {α : Type} (a : α) : Task ℭ q₀ α where
  fn _ [_] _ _ := Pure.pure a
  param A _ _ _ _ _ _ := A.rel_pure rfl

@[inline] def bind {α β : Type} (m : Task ℭ q₀ α) (k : α → Task ℭ q₀ β) :
    Task ℭ q₀ β where
  fn := fun g [_] inp fe => m.fn g inp fe >>= fun a => (k a).fn g inp fe
  param A _ _ f₁ f₂ hι hfe :=
    A.rel_bind (m.param A f₁ f₂ hι hfe)
      (fun a _ hab => hab ▸ (k a).param A f₁ f₂ hι hfe)

instance : Monad (Task ℭ q₀) where
  pure := pure
  bind := bind

@[inline] def input (i : ℭ.I) : Task ℭ q₀ (ℭ.V i) where
  fn := fun _ [_] inp _ => inp i
  param _ _ _ _ _ hι _ := hι i

@[inline] def fetch (q : ℭ.Q) (h : ℭ.rel q q₀) : Task ℭ q₀ (ℭ.R q) where
  fn := fun _ [_] _ fe => fe q h
  param _ _ _ _ _ _ hfe := hfe q h

instance instCoeFun {ℭ : BuildConfig} {q₀ : ℭ.Q} {α : Type} :
    CoeFun (Task ℭ q₀ α)
      (fun _ => ∀ (f : Type → Type) [Monad f],
        (∀ i, f (ℭ.V i)) → (∀ q, ℭ.rel q q₀ → f (ℭ.R q)) → f α) :=
  ⟨Task.fn⟩

end Task

export Task (input fetch)

class Input (ℭ : BuildConfig) (J : Type) where
  get : J → ∀ i, ℭ.V i
  set : J → ∀ i, ℭ.V i → J
  get_set_self : ∀ j i v, get (set j i v) i = v
  get_set_other : ∀ j i v i', i' ≠ i → get (set j i v) i' = get j i'

instance {ℭ : BuildConfig} [DecidableEq ℭ.I] : Input ℭ (∀ i, ℭ.V i) where
  get := id
  set := Function.update
  get_set_self _ _ _ := Function.update_self ..
  get_set_other _ _ _ _ h := Function.update_of_ne h ..

def Tasks (ℭ : BuildConfig) : Type 1 :=
  ∀ q₀, Task ℭ q₀ (ℭ.R q₀)

def compute {ℭ : BuildConfig} (tasks : Tasks ℭ)
    (ι : ∀ i, ℭ.V i) (q : ℭ.Q) : ℭ.R q :=
  (tasks q).fn Id ι (fun q' _ => compute tasks ι q')
termination_by ℭ.wf.wrap q

structure Value {ℭ : BuildConfig}
    (tasks : Tasks ℭ) (ι : ∀ i, ℭ.V i) (q : ℭ.Q) where
  val : ℭ.R q
  spec : val = compute tasks ι q

structure Build (ℭ : BuildConfig) (J : Type) [Input ℭ J] (tasks : Tasks ℭ)
    (n m : Type → Type) : Type 1 where
  σ : Type
  init : J → σ
  inputs : σ → ∀ i, ℭ.V i
  set : ∀ i, ℭ.V i → StateM σ Unit
  build : ∀ q store, n (m (Value tasks (inputs store) q) × σ)

def Build.run
    {ℭ : BuildConfig}
    {J : Type} [Input ℭ J]
    {tasks : Tasks ℭ}
    {n m : Type → Type} [Functor n] [Functor m]
    (b : Build ℭ J tasks n m) (q : ℭ.Q) : StateT b.σ n (m (ℭ.R q)) :=
  fun store => Prod.map (Value.val <$> ·) id <$> b.build q store

theorem Tasks.freeTheorem {ℭ : BuildConfig}
    {κ : Type → Type} [Monad κ]
    (tasks : Tasks ℭ) (q₀ : ℭ.Q)
    (F : MonadAction κ Id)
    (ι₀ : ∀ i, ℭ.V i)
    (ι₁ : ∀ i, κ (ℭ.V i))
    (fetch₁ : ∀ q, ℭ.rel q q₀ → κ (ℭ.R q))
    (hι : ∀ i, F.rel Eq (ι₁ i) (ι₀ i))
    (hfetch : ∀ q hq, F.rel Eq (fetch₁ q hq) (compute tasks ι₀ q)) :
    F.rel Eq ((tasks q₀).fn κ ι₁ fetch₁) (compute tasks ι₀ q₀) := by
  conv => rhs; unfold compute
  exact (tasks q₀).param F fetch₁ _ hι hfetch

end Incremental
