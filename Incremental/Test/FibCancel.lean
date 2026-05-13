import Incremental.Shake.Cancel
import Incremental.Test.Fibonacci

open Incremental
open Incremental.Test.Fibonacci
open Std (DHashMap)

namespace Incremental.Test.FibCancel

abbrev hI : ∀ i, config.V i ↪ UInt64 := nofun
abbrev hR : ∀ q, config.R q ↪ UInt64 := fun _ => Hashable.toEmbedding

def assert (cond : Bool) (msg : String) : IO Unit := do
  if !cond then throw (IO.userError msg)

#eval show IO Unit from do
  let cancelRef ← IO.mkRef false
  let b := ShakeCancel config Unit hI hR tasks cancelRef
  let (result, (_, cache)) ← b.build 30 (b.init ())
  match result with
  | .ok v =>
    assert (v.val == 832040) s!"fib 30 expected 832040, got {v.val}"
    assert (cache.size == 31) s!"expected 31 memos, got {cache.size}"
  | .error _ => throw (IO.userError "no-cancel run unexpectedly cancelled")

#eval show IO Unit from do
  let cancelRef ← IO.mkRef true
  let b := ShakeCancel config Unit hI hR tasks cancelRef
  let (result, (_, cache)) ← b.build 30 (b.init ())
  match result with
  | .ok _ => throw (IO.userError "pre-cancelled run unexpectedly succeeded")
  | .error _ =>
    assert (cache.size == 0) s!"expected 0 memos before any work, got {cache.size}"

#eval show IO Unit from do
  let cancelRef ← IO.mkRef false
  let counterRef ← IO.mkRef 0
  let onPersist (_q : config.Q) : BaseIO Unit := do
    let n ← counterRef.modifyGet (fun n => (n + 1, n + 1))
    if n == 10 then cancelRef.set true
  let b := ShakeCancel config Unit hI hR tasks cancelRef onPersist
  let (result, (_, cache)) ← b.build 40 (b.init ())
  let count ← counterRef.get
  match result with
  | .ok _ => throw (IO.userError s!"expected cancellation; got success with {count} persists")
  | .error _ =>
    assert (count == 10) s!"expected cancel after 10 persists; got {count}"
    assert (cache.size == 10) s!"expected 10 memos preserved; got {cache.size}"

end Incremental.Test.FibCancel
