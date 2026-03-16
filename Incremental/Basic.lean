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

/-!
[Build systems à la carte]
The choice of the constraint `c` has concrete meanings:
- `c := Functor` - sequential only
- `c := Applicative` - static dependencies
- `c := Monad` - dynamic dependencies
-/

structure BuildConfig : Type 1 where
  I : Type
  V : I → Type
  Q : Type
  R : Q → Type
  rel : (∀ i, V i) → Q → Q → Prop
  wf : ∀ ι, WellFounded (rel ι)

variable
  (c : (Type → Type) → Type 1)
  (ℭ : BuildConfig)
  (ι₀ : ∀ i, ℭ.V i)
  (q₀ : ℭ.Q)

set_option checkBinderAnnotations false in
def Task (α : Type) : Type 1 :=
  ∀ (f : Type → Type) [c f], (∀ i, f (ℭ.V i)) → (∀ q, ℭ.rel ι₀ q q₀ → f (ℭ.R q)) → f α

namespace Task

variable
  {c : (Type → Type) → Type 1}
  {ℭ : BuildConfig}
  {ι₀ : ∀ i, ℭ.V i}
  {q₀ : ℭ.Q}

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

instance [DecidableEq ℭ.I] : Input ℭ (∀ i, ℭ.V i) where
  get := id
  set := Function.update

def Tasks : Type 1 :=
  ∀ ι₀ q₀, Task c ℭ ι₀ q₀ (ℭ.R q₀)

structure Build (J : Type) [Input ℭ J] : Type 1 where
  σ : Type
  init : J → σ
  inputs : σ → ∀ i, ℭ.V i
  set : ∀ i, ℭ.V i → StateM σ Unit
  build : Tasks c ℭ → ∀ q, StateM σ (ℭ.R q)

end Incremental
