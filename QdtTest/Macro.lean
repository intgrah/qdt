import Qdt
import Qdt.Incremental
import Qdt.Frontend.Macro

open Qdt
open Qdt.Incremental (Engine Key Val TaskM)
open Lean (Term MacroM)

private def elabProg (prog : Frontend.Cst.Program) : IO (Except Error Incremental.GlobalEnv) := do
  let config : Config := Config.empty
  let engine : Engine Error Val := Incremental.newEngine
  let task : TaskM Error Val Incremental.GlobalEnv := do
    let prog := Frontend.Cst.Program.desugar prog
    let coreCtx : CoreContext := CoreContext.empty
    let init : CoreState := {
      modules := Std.HashMap.emptyWithCapacity 8
      importedEnv := Std.HashMap.emptyWithCapacity 128
      localEnv := Std.HashMap.emptyWithCapacity 128
      errors := #[]
    }
    let action : CoreM CoreState := do
      for cmd in prog do
        match cmd with
        | .import _ => pure ()
        | .definition d => elabDefinition d
        | .example ex => elabExample ex
        | .axiom a => elabAxiom a
        | .inductive i => elabInductiveCmd i
        | .structure s => elabStructureCmd s
      get
    let st ← (action.run coreCtx).run' init
    if st.errors.isEmpty then
      pure st.localEnv
    else
      throw st.errors[0]!
  match ← Incremental.run config engine task with
  | .ok (env, _) => pure (.ok env)
  | .error e => pure (.error e)

private def shouldPass (prog : Frontend.Cst.Program) : IO Unit := do
  match ← elabProg prog with
  | .ok _ => pure ()
  | .error e => throw (IO.userError s!"expected success, got: {e}")

private def shouldFail (check : Error → Bool) (prog : Frontend.Cst.Program) : IO Unit := do
  match ← elabProg prog with
  | .ok _ => throw (IO.userError "expected error, got success")
  | .error e =>
      if check e then pure ()
      else throw (IO.userError s!"wrong error: {e}")

private def termListExpr (xs : List Term) : MacroM Term := do
  let xsArray := xs.toArray
  `([$[$xsArray],*])

/--
`#pass (prog)` expects `prog` to elaborate successfully.
-/
syntax "#pass" "(" command* ")" : command

macro_rules
  | `(command| #pass ($[$cs:command]*)) => do
      let cmdTerms ← cs.mapM fun c => Frontend.Macro.cmd c.raw
      let prog ← termListExpr cmdTerms.toList
      `(command| #eval shouldPass $prog)

/--
`#fail (prog) with pat` expects `prog` to fail with
an error matching `pat`.
-/
syntax "#fail" "(" command* ")" "with" term : command

macro_rules
  | `(command| #fail ($[$cs:command]*) with $pat:term) => do
      let cmdTerms ← cs.mapM fun c => Frontend.Macro.cmd c.raw
      let prog ← termListExpr cmdTerms.toList
      `(command| #eval shouldFail (· matches $pat) $prog)
