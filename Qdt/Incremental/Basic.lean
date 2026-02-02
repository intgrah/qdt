import Std.Data.DHashMap
import Std.Data.HashMap
import Std.Data.HashSet
import Qdt.Incremental.Theory

namespace Qdt.Incremental

open Std (HashMap DHashMap HashSet)

variable {ε α Q : Type} {R : Q → Type} [BEq Q] [LawfulBEq Q] [Hashable Q]

structure Memo (R : Q → Type) (q : Q) where
  value : R q
  deps : HashMap Q UInt64

abbrev Cache (R : Q → Type) [BEq Q] [Hashable Q] := DHashMap Q (Memo R)
abbrev ReverseDeps (Q : Type) [BEq Q] [Hashable Q] := HashMap Q (HashSet Q)

structure Engine (ε : Type) (R : Q → Type) where
  cache : Cache R := DHashMap.emptyWithCapacity 1024
  reverseDeps : ReverseDeps Q := HashMap.emptyWithCapacity 1024
  recover : (q : Q) → EIO ε (R q)
  fingerprint : ∀ q, R q → UInt64
  isInput : Q → Bool

namespace Engine

def addReverseDep (engine : Engine ε R) (dependency dependent : Q) : Engine ε R :=
  let existing := engine.reverseDeps.getD dependency (HashSet.emptyWithCapacity 8)
  { engine with reverseDeps := engine.reverseDeps.insert dependency (existing.insert dependent) }

partial def getTransitiveDependents (engine : Engine ε R) (keys : HashSet Q) : HashSet Q :=
  let rec go (worklist : List Q) (visited : HashSet Q) : HashSet Q :=
    match worklist with
    | [] => visited
    | k :: rest =>
        if visited.contains k then
          go rest visited
        else
          let visited := visited.insert k
          let dependents := engine.reverseDeps.getD k (HashSet.emptyWithCapacity 0)
          let newWork := dependents.toList.filter (!visited.contains ·)
          go (newWork ++ rest) visited
  go keys.toList (HashSet.emptyWithCapacity keys.size)

def invalidate (engine : Engine ε R) (changedKeys : HashSet Q) : Engine ε R :=
  let toInvalidate := engine.getTransitiveDependents changedKeys
  let newCache := toInvalidate.fold (init := engine.cache) fun cache key =>
    cache.erase key
  { engine with cache := newCache }

def invalidateFiles (engine : Engine ε R) (changedFiles : List Q) : Engine ε R :=
  let changedSet := changedFiles.foldl (init := HashSet.emptyWithCapacity changedFiles.length) (·.insert ·)
  engine.invalidate changedSet

end Engine

structure RunState (ε : Type) (R : Q → Type) where
  engine : Engine ε R
  started : Cache R
  stack : List Q
  deps : HashMap Q UInt64

abbrev BaseM (ε : Type) {Q : Type} (R : Q → Type) [BEq Q] [Hashable Q] := StateRefT (RunState ε R) (EIO ε)
abbrev TaskM (ε : Type) {Q : Type} (R : Q → Type) [BEq Q] [Hashable Q] := Incremental.TaskT Q R (BaseM ε R)

def TaskM.fetch (q : Q) : TaskM ε R (R q) := Incremental.TaskT.fetch q

end Qdt.Incremental
