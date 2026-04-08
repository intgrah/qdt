module

public import Std.Data.DHashMap
public import Std.Data.HashMap
public import Std.Data.HashSet

@[expose] public section

namespace Incremental

open Std (DHashMap HashMap HashSet)

/-!
[Build systems à la carte]
The choice of the constraint `c` has concrete meanings:
- `c := Functor` - sequential only
- `c := Applicative` - static dependencies
- `c := Monad` - dynamic dependencies
-/

set_option checkBinderAnnotations false

structure BuildConfig : Type 1 where
  I : Type
  V : I → Type
  Q : Type
  R : Q → Type
  rel : (∀ i, V i) → Q → Q → Prop
  wf : ∀ ι, WellFounded (rel ι)

variable
  (c : (Type → Type) → Type 1) [hc : c Id] (ℭ : BuildConfig)
  (ι₀ : ∀ i, ℭ.V i) (q₀ : ℭ.Q)
  (m : Type → Type)

def Task (α : Type) : Type 1 :=
  ∀ (f : Type → Type) [c f],
  (ι : ∀ i, f (ℭ.V i)) →
  (∀ q, ℭ.rel ι₀ q q₀ → f (ℭ.R q)) →
  f α

namespace Task

variable
  {c : (Type → Type) → Type 1} {ℭ : BuildConfig}
  {ι₀ : ∀ i, ℭ.V i} {q₀ : ℭ.Q}

def input (i : ℭ.I) :
    Task c ℭ ι₀ q₀ (ℭ.V i) :=
  fun _ [_] input _ => input i

def fetch (q : ℭ.Q) (h : ℭ.rel ι₀ q q₀) :
    Task c ℭ ι₀ q₀ (ℭ.R q) :=
  fun _ [_] _ fetch => fetch q h

instance : Monad (Task Monad ℭ ι₀ q₀) where
  pure a := fun _ [_] _ _ => pure a
  bind t f := fun g [_] input fetch => t g input fetch >>= fun a => f a g input fetch
  map f t := fun g [_] input fetch => f <$> t g input fetch

end Task

export Task (input fetch)

class Input (J : Type) where
  get : J → ∀ i, ℭ.V i
  set : J → ∀ i, ℭ.V i → J

def Tasks : Type 1 :=
  ∀ ι₀ q₀, Task c ℭ ι₀ q₀ (ℭ.R q₀)

set_option linter.unusedVariables false in
def Tasks.eval
    {c : (Type → Type) → Type 1} [hc : c Id]
    {ℭ : BuildConfig} (tasks : Tasks c ℭ)
    (ι₀ : ∀ i, ℭ.V i) (q₀ : ℭ.Q) : ℭ.R q₀ :=
  @tasks ι₀ q₀ Id hc ι₀ (fun q hq => tasks.eval (hc := hc) ι₀ q)
termination_by (ℭ.wf ι₀).wrap q₀
decreasing_by exact hq

structure Build (J : Type) [Input ℭ J] : Type 1 where
  σ : Type
  init : J → σ
  inputs : σ → ∀ i, ℭ.V i
  set : ∀ i, ℭ.V i → σ → σ
  build :
    ∀ (tasks : Tasks c ℭ) (store : σ) (q₀ : ℭ.Q),
    m ({ r : ℭ.R q₀ // r = tasks.eval (hc := hc) (inputs store) q₀ } × σ)

end Incremental
