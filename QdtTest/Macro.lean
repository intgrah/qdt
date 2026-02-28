import Qdt
import Qdt.Incremental

open Qdt
open Incremental (Engine Key Val TaskM BaseContext)
open Lean (Term MacroM)

private def elabProgFromString (src : String) : IO (Array Diagnostic × Global) := do
  let cst := match Frontend.Parser.parse src with
    | .ok cst => cst
    | .error e => panic! s!"parse error at {e.pos}: {e.msg}"
  let config : Config := Config.empty
  let ctx : BaseContext := { config, overrides := ∅ }
  let engine : Engine Val := Incremental.newEngine
  let (asts, _) := Frontend.desugarProgram cst
  let task : TaskM Val (Array Diagnostic × Global) := do
    let coreCtx : CoreContext := CoreContext.empty
    let init : CoreState := {
      modules := Std.HashMap.emptyWithCapacity 8
      importedEnv := Std.HashMap.emptyWithCapacity 128
      localEnv := Std.HashMap.emptyWithCapacity 128
      errors := #[]
    }
    let action : CoreM CoreState := do
      for ast in asts do
        if let some d := parseDefinition ast then elabDefinition d
        else if let some ex := parseExample ast then elabExample ex
        else if let some a := parseAxiom ast then elabAxiom a
        else if let some i := parseInductive ast then elabInductiveCmd i
        else if let some s := parseStructure ast then elabStructureCmd s
      get
    let ((result, elabInfo), st) ← ((action.run coreCtx).run.run).run init
    let diagnostics := elabInfo.diagnostics
    match result with
    | .ok s => return (diagnostics, s.localEnv)
    | .error e => return (diagnostics.push { path := [], error := e }, st.localEnv)
  match ← (Incremental.run ctx engine task).toIO' with
  | .ok ((diagnostics, env), _) => pure (diagnostics, env)
  | .error () => pure (#[{ path := [], error := .msg "cycle detected" }], ∅)

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
