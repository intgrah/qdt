import Incremental.Shake.Trace
import Incremental.LawfulEST
import Incremental.Test.Fibonacci

namespace Incremental.Test.FibTrace

open Incremental Incremental.Test.Fibonacci

def build : Build config Unit tasks (Trace.TraceT Nat BaseIO) Id :=
  ShakeTrace config Unit nofun (fun _ => Hashable.toEmbedding) tasks

def runOnce (q : Nat) : StateT build.σ BaseIO (Nat × Trace.Forest Nat) := fun s => do
  let ((r, s'), forest) ← Trace.run (StateT.run (s := s) (build.run q))
  pure ((r, forest), s')

partial def DepNode.lines : Trace.DepNode Nat → String → String → List String
  | ⟨q, _, children⟩, prefixHere, prefixRest =>
    let head := prefixHere ++ s!"fib {q}"
    let n := children.size
    let childLines := children.toList.zipIdx.flatMap fun (c, i) =>
      let isLast := i + 1 == n
      let here := prefixRest ++ (if isLast then "└─ " else "├─ ")
      let rest := prefixRest ++ (if isLast then "   " else "│  ")
      DepNode.lines c here rest
    head :: childLines

instance : ToString (Trace.Forest Nat) where
  toString f := String.intercalate "\n" (f.toList.flatMap fun root => DepNode.lines root "" "")

def script : StateT build.σ BaseIO (List (Nat × Trace.Forest Nat)) := do
  return [
    ← runOnce 6,
    ← runOnce 5,
    ← runOnce 5,
    ← runOnce 5,
    ← runOnce 8,
  ]

/--
info:
fib 6
├─ fib 5
│  ├─ fib 4
│  │  ├─ fib 3
│  │  │  ├─ fib 2
│  │  │  │  ├─ fib 1
│  │  │  │  └─ fib 0
│  │  │  └─ fib 1
│  │  └─ fib 2
│  └─ fib 3
└─ fib 4

fib 5

fib 5

fib 5

fib 8
├─ fib 7
│  ├─ fib 6
│  └─ fib 5
└─ fib 6
-/
#guard_msgs in
#eval show IO Unit from do
  let ds ← script.run' (build.init ())
  for ⟨_, forest⟩ in ds do
    println! forest
    println! ""

end Incremental.Test.FibTrace
