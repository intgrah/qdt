module

public import Mathlib.Logic.Function.Basic
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

variable
  (c : (Type → Type) → Type 1)
  (I : Type) (V : I → Type)
  (Q : Type) (R : Q → Type)

set_option checkBinderAnnotations false in
def Task (α : Type) : Type 1 :=
  ∀ (f : Type → Type) [c f], (∀ i, V i) → (∀ q, f (R q)) → f α

namespace Task

variable
  {c : (Type → Type) → Type 1}
  {I : Type} {V : I → Type}
  {Q : Type} {R : Q → Type}

def input (i : I) :
    Task Monad I V Q R (V i) :=
  fun _ [_] iv _ => pure (iv i)

def fetch (q : Q) :
    Task c I V Q R (R q) :=
  fun _ [_] _ fetch => fetch q

instance {I : Type} {V : I → Type} {Q : Type} {R : Q → Type} :
    Monad (Task Monad I V Q R) where
  pure a := fun _ [_] _ _ => pure a
  bind t f := fun g [_] input fetch => t g input fetch >>= fun a => f a g input fetch
  map f t := fun g [_] input fetch => f <$> t g input fetch

end Task

export Task (input fetch)

class Input (I : Type) (V : I → Type) (ι : Type) where
  get : ι → ∀ i, V i
  set : ι → ∀ i, V i → ι

instance {I : Type} {V : I → Type} [DecidableEq I] : Input I V (∀ i, V i) where
  get := id
  set := Function.update

instance {I : Type} {V : I → Type} [BEq I] [LawfulBEq I] [Hashable I] :
    Input I (fun i => Option (V i)) (DHashMap I V) where
  get := DHashMap.get?
  set m i v := m.alter i (fun _ => v)

instance {α n} : Input (Fin n) (fun _ => α) (Vector α n) where
  get vec i := vec.get i
  set vec i := vec.set i

def Tasks : Type 1 :=
  ∀ q, Task c I V Q R (R q)

inductive BuildError where
  | cycle
deriving Inhabited

structure Build (ι : Type) [Input I V ι] : Type 1 where
  σ : Type
  init : ι → σ
  set : σ → ∀ i, V i → σ
  build : Tasks c I V Q R → ∀ q, σ → Except BuildError (R q × σ)

end Incremental
