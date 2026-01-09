import Qdt
import Qdt.IncrementalElab
import Lake.Util.Cli

open Qdt
open Incremental (Engine TaskM TopDecl Key Val)

private def topDecls : Frontend.Ast.Program → List TopDecl :=
  List.filterMap
    (fun
      | .definition d => some ⟨.definition, d.name⟩
      | .axiom a => some ⟨.axiom, a.name⟩
      | .inductive i => some ⟨.inductive, i.name⟩
      | .structure s => some ⟨.structure, s.name⟩
      | .example _ => none
      | .import _ => none)

structure EntryCounts where
  definitions : Nat
  axioms : Nat
  inductives : Nat
  recursors : Nat
  constructors : Nat
  opaques : Nat
  total : Nat

private def countEntries (file : System.FilePath) :
    TaskM Error Val EntryCounts := do
  let mut definitions := 0
  let mut opaques := 0
  let mut axioms := 0
  let mut inductives := 0
  let mut recursors := 0
  let mut constructors := 0
  let mut total := 0

  let prog : Frontend.Ast.Program ←
    TaskM.fetch (Key.astProgram file)

  for decl in topDecls prog do
    try
      let env : Std.HashMap Lean.Name Entry ←
        TaskM.fetch (Key.elabTop file decl)
      total := total + env.size

      for entry in env.values do
        match entry with
        | .definition .. => definitions := definitions + 1
        | .opaque .. => opaques := opaques + 1
        | .axiom .. => axioms := axioms + 1
        | .inductive .. => inductives := inductives + 1
        | .recursor .. => recursors := recursors + 1
        | .constructor .. => constructors := constructors + 1

    catch err =>
      IO.toEIO Error.ioError <|
        IO.println s!"[error] {decl.name}: {err}"
      break

  return {
    definitions,
    axioms,
    inductives,
    recursors,
    constructors,
    opaques,
    total,
  }

private def runOnce (engine : Engine Error Val) (file : System.FilePath) : IO (Engine Error Val) := do
  let res ← (Incremental.run engine (countEntries file)).toIO'
  match res with
  | .ok (counts, engine') =>
      IO.println s!"Definitions: {counts.definitions}"
      IO.println s!"Axioms: {counts.axioms}"
      IO.println s!"Inductives: {counts.inductives}"
      IO.println s!"Recursors: {counts.recursors}"
      IO.println s!"Constructors: {counts.constructors}"
      IO.println s!"Opaques: {counts.opaques}"
      IO.println s!"Total entries: {counts.total}"
      pure engine'
  | .error err =>
      IO.println s!"[error] {err}"
      pure engine

partial def watchLoop (engine : Engine Error Val) (file : System.FilePath) : IO Unit := do
  let mut last : Option UInt64 := none
  let mut engine := engine
  while true do
    let content ← IO.FS.readFile file
    let h := hash content
    if last != some h then
      last := some h
      IO.println s!"\n=== change detected ==="
      engine ← runOnce engine file
    IO.sleep 200

def main (args : List String) : IO Unit := do
  let watch := args.contains "--watch"
  let twice := args.contains "--twice"
  let args := args.filter (fun s => s != "--watch" && s != "--twice")
  let filePath : System.FilePath :=
    match args with
    | path :: _ => path
    | [] => "../stdlib/stdlib.qdt"
  let engine : Engine Error Val := Incremental.newEngine
  if watch then
    IO.println s!"Watching {filePath} (poll)"
    watchLoop engine filePath
  else
    if twice then
      let t0 ← IO.monoMsNow
      let engine ← runOnce engine filePath
      let t1 ← IO.monoMsNow
      IO.println s!"[time] run1 {t1 - t0}ms"
      let t2 ← IO.monoMsNow
      let _engine ← runOnce engine filePath
      let t3 ← IO.monoMsNow
      IO.println s!"[time] run2 {t3 - t2}ms"
    else
      let _engine ← runOnce engine filePath
