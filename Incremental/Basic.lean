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

set_option checkBinderAnnotations false in
def Task
    (c : (Type → Type) → Type 1)
    (Q : Type)
    (R : Q → Type)
    (α : Type) :
    Type 1 :=
  ∀ (f : Type → Type) [c f], (∀ q, f (R q)) → f α

variable (c : (Type → Type) → Type 1) (σ : Type) (Q : Type) (R : Q → Type)

namespace Task

def fetch
    {c : (Type → Type) → Type 1}
    {Q : Type}
    {R : Q → Type}
    (q : Q) :
    Task c Q R (R q) :=
  fun _ [_] fetch => fetch q

instance {Q : Type} {R : Q → Type} : Monad (Task Monad Q R) where
  pure a := fun _ [_] _ => pure a
  bind t f := fun g [_] fetch => t g fetch >>= fun a => f a g fetch
  map f t := fun g [_] fetch => f <$> t g fetch

end Task

export Task (fetch)

inductive BuildError
  | cycle
  | missingInput
deriving Inhabited

def Tasks : Type 1 :=
  ∀ q, Option (Task c Q R (R q))

def Build : Type 1 :=
  Tasks c Q R → ∀ q, StateT σ (Except BuildError) (R q)

end Incremental
