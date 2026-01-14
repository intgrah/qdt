import Std.Data.HashMap
import Std.Data.HashSet

import Qdt.Bidirectional
import Qdt.Error
import Qdt.Frontend.Ast
import Qdt.MLTT.Global
import Qdt.Nbe
import Qdt.Params
import Qdt.Quote
import Qdt.Frontend.Desugar
import Qdt.Inductive
import Qdt.Structure

namespace Qdt

open Lean (Name)

def findModule? (name : Name) : CoreM (Option ModuleStatus) := do
  return (← getThe CoreState).modules[name]?

def addModule (name : Name) (status : ModuleStatus) : CoreM Unit := do
  modifyThe CoreState fun st => { st with modules := st.modules.insert name status }

private def checkDuplicateUnivParams (src : Frontend.Src) (params : List Name) :
    CoreM Unit := do
  let rec loop (seen : Std.HashSet Name) : List Name → CoreM Unit
    | [] => pure ()
    | n :: ns =>
        if seen.contains n then
          throw (.duplicateUniverseParam src n)
        else
          loop (seen.insert n) ns
  loop {} params

def elabDefinition (d : Frontend.Ast.Command.Definition) : CoreM Unit := do
  checkDuplicateUnivParams d.src d.univParams
  let metaAction : MetaM (Tm 0 × Ty 0) := do
    let (paramCtx, paramTys) ← elabParams d.params
    let (tm, ty) ←
      match d.tyOpt with
      | none =>
          let (tm, tyVal) ← inferTm d.body paramCtx
          let ty ← tyVal.quote
          pure (tm, ty)
      | some tyRaw =>
          let ty ← checkTy tyRaw paramCtx
          let tyVal ← ty.eval paramCtx.env
          let tm ← checkTm tyVal d.body paramCtx
          pure (tm, ty)
    let tm := Tm.lams paramTys tm
    let ty := Ty.pis paramTys ty
    return (tm, ty)
  let mctx : MetaContext := { MetaContext.empty with currentDecl := d.name }
  let (tm, ty) ← (metaAction mctx).run' { univParams := d.univParams }
  Global.addEntry d.name (.definition { univParams := d.univParams, ty, tm })

def elabExample (e : Frontend.Ast.Command.Example) : CoreM Unit := do
  checkDuplicateUnivParams e.src e.univParams
  let metaAction : MetaM Unit := do
    let (paramCtx, _paramTys) ← elabParams e.params
    match e.tyOpt with
    | some tyRaw =>
        let expected ← checkTy tyRaw paramCtx
        let expected ← expected.eval paramCtx.env
        let _term ← checkTm expected e.body paramCtx
    | none =>
        let (_term, _tyVal) ← inferTm e.body paramCtx
  (metaAction MetaContext.empty).run' { univParams := e.univParams }

def elabAxiom (a : Frontend.Ast.Command.Axiom) : CoreM Unit := do
  checkDuplicateUnivParams a.src a.univParams
  let metaAction : MetaM Unit := do
    let (paramCtx, paramTys) ← elabParams a.params
    let ty ← checkTy a.ty paramCtx
    let ty := Ty.pis paramTys ty
    Global.addEntry a.name (.axiom { univParams := a.univParams, ty })
  let mctx : MetaContext := { MetaContext.empty with currentDecl := a.name }
  (metaAction mctx).run' { univParams := a.univParams }

def elabInductiveCmd (info : Frontend.Ast.Command.Inductive) : CoreM Unit := do
  checkDuplicateUnivParams info.src info.univParams
  let mctx : MetaContext := { MetaContext.empty with currentDecl := info.name }
  (elabInductive info mctx).run' { univParams := info.univParams }

def elabStructureCmd (info : Frontend.Ast.Command.Structure) : CoreM Unit := do
  checkDuplicateUnivParams info.src info.univParams
  let mctx : MetaContext := { MetaContext.empty with currentDecl := info.name }
  (elabStructure info mctx).run' { univParams := info.univParams }

def protectUnit
    (k : CoreM Unit) :
    CoreM Unit := do
  try
    k
  catch err =>
    modify fun st => { st with errors := st.errors.push err }

def processImport
    (filename : System.FilePath)
    (m : Frontend.Ast.Command.Import)
    : CoreM Unit := do
  let name := m.moduleName
  match ← findModule? name with
  | some .imported => return
  | some .importing => throw (.msg "Circular import")
  | none =>
      addModule name .importing
      let _content ←
        try
          pure (IO.FS.readFile filename)
        catch _err =>
          throw (.msg s!"Error in {filename}")
      addModule name .imported

def elabProgramWithImports
    (currentFile : System.FilePath)
    (prog : Frontend.Ast.Program) :
    CoreM Unit := do
  for cmd in prog do
    protectUnit (
      match cmd with
      | .import m => processImport currentFile m
      | .definition d => elabDefinition d
      | .example ex => elabExample ex
      | .axiom ax => elabAxiom ax
      | .inductive info => elabInductiveCmd info
      | .structure info => elabStructureCmd info)

end Qdt
