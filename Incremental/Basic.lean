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

variable
  (c : (Type → Type) → Type 1)
  (ℭ : BuildConfig)
  (q₀ : ℭ.Q)

set_option checkBinderAnnotations false in
def Task (α : Type) : Type 1 :=
  ∀ (f : Type → Type) [c f], (∀ i, f (ℭ.V i)) → (∀ q, ℭ.rel q q₀ → f (ℭ.R q)) → f α

namespace Task

variable
  {c : (Type → Type) → Type 1}
  {ℭ : BuildConfig}
  {q₀ : ℭ.Q}

def input (i : ℭ.I) :
    Task c ℭ q₀ (ℭ.V i) :=
  fun _ [_] input _ => input i

def fetch (q : ℭ.Q) (h : ℭ.rel q q₀) :
    Task c ℭ q₀ (ℭ.R q) :=
  fun _ [_] _ fetch => fetch q h

instance : Monad (Task Monad ℭ q₀) where
  pure a := fun _ [_] _ _ => pure a
  bind t f := fun g [_] input fetch => t g input fetch >>= fun a => f a g input fetch
  map f t := fun g [_] input fetch => f <$> t g input fetch

end Task

export Task (input fetch)

class Input (J : Type) where
  get : J → ∀ i, ℭ.V i
  set : J → ∀ i, ℭ.V i → J
  get_set_self : ∀ j i v, get (set j i v) i = v
  get_set_other : ∀ j i v i', i' ≠ i → get (set j i v) i' = get j i'

instance [DecidableEq ℭ.I] : Input ℭ (∀ i, ℭ.V i) where
  get := id
  set := Function.update
  get_set_self _ _ _ := Function.update_self ..
  get_set_other _ _ _ _ h := Function.update_of_ne h ..

def Tasks : Type 1 :=
  ∀ q₀, Task c ℭ q₀ (ℭ.R q₀)

def compute {ℭ : BuildConfig} {c : (Type → Type) → Type 1}
    (cId : c Id) (tasks : Tasks c ℭ)
    (ι : ∀ i, ℭ.V i) (q : ℭ.Q) : ℭ.R q :=
  @tasks q Id cId ι (fun q' _ => compute cId tasks ι q')
termination_by ℭ.wf.wrap q

structure Build (c : (Type → Type) → Type 1)
    (ℭ : BuildConfig) (J : Type) [Input ℭ J] (tasks : Tasks c ℭ)
    (m : Type → Type) : Type 1 where
  cId : c Id
  σ : Type
  init : J → σ
  inputs : σ → ∀ i, ℭ.V i
  set : ∀ i, ℭ.V i → StateM σ Unit
  build : (q : ℭ.Q) → (store : σ) →
    m ({ r : ℭ.R q // r = compute cId tasks (inputs store) q } × σ)

def Build.run
    {c : (Type → Type) → Type 1}
    {ℭ : BuildConfig}
    {J : Type} [Input ℭ J]
    {tasks : Tasks c ℭ}
    {m : Type → Type} [Monad m]
    (b : Build c ℭ J tasks m) (q : ℭ.Q) : StateT b.σ m (ℭ.R q) := do
  let store ← get
  let (⟨r, _⟩, store) ← b.build q store
  StateT.set store
  return r

end Incremental
