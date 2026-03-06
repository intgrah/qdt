import Qdt
import Qdt.Incremental

open Qdt
open Qdt.Incremental
open Lean (Term MacroM)
open System (FilePath)
open Std (DHashMap)

private def elabProgFromString (src : String) : IO (Array Diagnostic × Global) := do
  let dummyPath : FilePath := "test.qdt"
  let memo : Memo Key Val (.text dummyPath) := { value := src, deps := ∅, hash := hash src }
  let inputFiles : Std.HashSet System.FilePath := Std.HashSet.emptyWithCapacity 1 |>.insert dummyPath
  let inputMemo : Memo Key Val .inputFiles := { value := inputFiles, deps := ∅, hash := hash inputFiles }
  let store : Store Key Val := { cache := DHashMap.emptyWithCapacity 2 }
  let store := { store with cache := store.cache.insert (.text dummyPath) memo }
  let store := { store with cache := store.cache.insert .inputFiles inputMemo }

  match ← (Incremental.run (Build.shake Key Val) store (Incremental.Task.fetch (Key.checkFile dummyPath))).toIO' with
  | .ok (diags, _) => return (diags, ∅)
  | .error () => return (#[{ path := [], error := .msg "cycle detected" }], ∅)

private def shouldPass (src : String) : IO Unit := do
  let (diagnostics, _) ← elabProgFromString src
  if diagnostics.isEmpty then
    pure ()
  else
    throw (IO.userError s!"expected success, got: {diagnostics[0]!.error}")

private def shouldFail (check : Error → Bool) (src : String) : IO Unit := do
  let (diagnostics, _) ← elabProgFromString src
  if diagnostics.isEmpty then
    throw (IO.userError "expected error, got success")
  else
    let err := diagnostics[0]!.error
    if check err then pure ()
    else throw (IO.userError s!"wrong error: {err}")

/--
`#pass (prog)` expects `prog` to elaborate successfully.
-/
syntax "#pass" "(" command* ")" : command

macro_rules
  | `(command| #pass ($[$cs:command]*)) => do
      let src := String.intercalate "\n" (cs.toList.map (·.raw.prettyPrint.pretty))
      `(command| #eval shouldPass $(Lean.quote src))

/--
`#fail (prog) with pat` expects `prog` to fail with
an error matching `pat`.
-/
syntax "#fail" "(" command* ")" "with" term : command

macro_rules
  | `(command| #fail ($[$cs:command]*) with $pat:term) => do
      let src := String.intercalate "\n" (cs.toList.map (·.raw.prettyPrint.pretty))
      `(command| #eval shouldFail (· matches $pat) $(Lean.quote src))
