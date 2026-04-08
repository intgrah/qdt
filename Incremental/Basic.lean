module

public import Mathlib.Logic.Function.Basic
public import Std.Data.DHashMap
public import Std.Data.HashMap
public import Std.Data.HashSet
public import Incremental.Selective

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

instance [DecidableEq ℭ.I] : Input ℭ (∀ i, ℭ.V i) where
  get := id
  set := Function.update

def Tasks : Type 1 :=
  ∀ q₀, Task c ℭ q₀ (ℭ.R q₀)

/-! ## The naive evaluator (the spec)

`compute tasks ι q` runs `tasks` at the identity monad with `ι` for
inputs and `compute` itself for fetches. This is what `Busy` does;
every other build system must agree with it. -/

set_option linter.unusedVariables false in
set_option checkBinderAnnotations false in
/
with `ι` for inputs and the recursive `compute` for fetches.  The
spec every `Build c` is verified against.  The `cId : c Id`
witness is supplied explicitly because `c` is an ordinary
`(Type → Type) → Type 1` rather than a Lean typeclass. -/
def compute {ℭ : BuildConfig} {c : (Type → Type) → Type 1}
    (cId : c Id) (tasks : Tasks c ℭ)
    (ι : ∀ i, ℭ.V i) (q : ℭ.Q) : ℭ.R q :=
  @tasks q Id cId ι (fun q' _hq => compute cId tasks ι q')
termination_by ℭ.wf.wrap q
decreasing_by exact _hq

/-! ## Verified build systems

A `Build c` is a build implementation that produces values **paired
with a proof they equal `compute`**.  The constraint `c` controls
the level at which tasks are scheduled: `Applicative` for fully
static parallel dispatch, `Selective` for speculative parallel
prefetch with bounded over-approximation, `Monad` for the
suspending strategy that discovers deps dynamically. -/

/
gives a witness that `Id` satisfies `c`, used by `compute` in the
correctness statement.  For `c ∈ {Functor, Applicative, Selective,
Monad}` an instance for `Id` already exists; pass `inferInstance`. -/
structure Build (c : (Type → Type) → Type 1)
    (ℭ : BuildConfig) (J : Type) [Input ℭ J] : Type 1 where
  cId : c Id
  σ : Type
  init : J → σ
  inputs : σ → ∀ i, ℭ.V i
  set : ∀ i, ℭ.V i → StateM σ Unit
  /
  `r = compute tasks (inputs store) q`, plus an updated store. -/
  build :
    (tasks : Tasks c ℭ) → (q : ℭ.Q) → (store : σ) →
      { r : ℭ.R q // r = compute cId tasks (inputs store) q } × σ

/
(`Salsa`, `ShakeC`, `ShakeCPS`, etc.). -/
structure BuildLegacy (c : (Type → Type) → Type 1)
    (ℭ : BuildConfig) (J : Type) [Input ℭ J] : Type 1 where
  σ : Type
  init : J → σ
  inputs : σ → ∀ i, ℭ.V i
  set : ∀ i, ℭ.V i → StateM σ Unit
  build : Tasks c ℭ → ∀ q, StateM σ (ℭ.R q)

/
`BuildLegacy`. -/
def Build.toLegacy {c : (Type → Type) → Type 1}
    {ℭ : BuildConfig} {J : Type} [Input ℭ J]
    (b : Build c ℭ J) : BuildLegacy c ℭ J where
  σ := b.σ
  init := b.init
  inputs := b.inputs
  set := b.set
  build tasks q :=
    fun store =>
      let (⟨r, _⟩, store') := b.build tasks q store
      (r, store')

end Incremental
