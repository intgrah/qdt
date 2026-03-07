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

variable (c : (Type → Type) → Type 1) (Q : Type) (R : Q → Type)
  [BEq Q] [LawfulBEq Q] [Hashable Q] [∀ q, Hashable (R q)]

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

inductive Cycle
  | mk
deriving Inhabited

def Tasks : Type 1 :=
  ∀ q, Option (Task c Q R (R q))

structure Memo (q : Q) where
  value : R q
  deps : HashMap Q UInt64
  hash : UInt64
  hash_value : Hashable.hash value = hash := by rfl

structure Store where
  cache : DHashMap Q (Memo Q R) := DHashMap.emptyWithCapacity 1024
  reverseDeps : HashMap Q (HashSet Q) := HashMap.emptyWithCapacity 1024
deriving Inhabited

namespace Store

def addReverseDep (store : Store Q R) (dependency dependent : Q) : Store Q R :=
  let existing := store.reverseDeps.getD dependency ∅
  let existing := existing.insert dependent
  let reverseDeps := store.reverseDeps.insert dependency existing
  { store with reverseDeps }

partial def getTransitiveDependents (store : Store Q R) (keys : HashSet Q) : HashSet Q :=
  let rec go (worklist : List Q) (visited : HashSet Q) : HashSet Q :=
    match worklist with
    | [] => visited
    | k :: rest =>
        if visited.contains k then
          go rest visited
        else
          let visited := visited.insert k
          let dependents := store.reverseDeps.getD k (HashSet.emptyWithCapacity 0)
          let newWork := dependents.toList.filter (!visited.contains ·)
          go (newWork ++ rest) visited
  go keys.toList (HashSet.emptyWithCapacity keys.size)

def invalidate (store : Store Q R) (changedKeys : HashSet Q) : Store Q R :=
  let toInvalidate := store.getTransitiveDependents Q R changedKeys
  let cache := toInvalidate.fold (init := store.cache) DHashMap.erase
  { store with cache }

end Store

def Build : Type 1 :=
  Tasks c Q R → Q → Store Q R → Except Cycle (Store Q R)

end Incremental
