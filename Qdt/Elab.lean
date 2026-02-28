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
open Frontend (Ast)

structure Definition where
  name : Name
  univParams : List Name
  params : List Ast
  tyOpt : Option Ast
  body : Ast

structure Example where
  univParams : List Name
  params : List Ast
  tyOpt : Option Ast
  body : Ast

structure Axiom where
  name : Name
  univParams : List Name
  params : List Ast
  ty : Ast

structure Import where
  moduleName : Name

def parseDefinition : Ast → Option Definition
  | .node `Command.definition #[.ident name, .node `null univParamsAst, .node `null paramsAst, tyOpt, body] =>
      let univParams := univParamsAst.toList.filterMap fun | .ident n => some n | _ => none
      let tyOpt := if tyOpt.kind? == some `null || tyOpt == .missing then none else some tyOpt
      some { name, univParams, params := paramsAst.toList, tyOpt, body }
  | _ => none

def parseExample : Ast → Option Example
  | .node `Command.example #[.node `null paramsAst, tyOpt, body] =>
      let tyOpt := if tyOpt.kind? == some `null || tyOpt == .missing then none else some tyOpt
      some { univParams := [], params := paramsAst.toList, tyOpt, body }
  | _ => none

def parseAxiom : Ast → Option Axiom
  | .node `Command.axiom #[.ident name, .node `null univParamsAst, .node `null paramsAst, ty] =>
      let univParams := univParamsAst.toList.filterMap fun | .ident n => some n | _ => none
      some { name, univParams, params := paramsAst.toList, ty }
  | _ => none

def parseImport : Ast → Option Import
  | .node `Command.import #[.ident moduleName] => some { moduleName }
  | _ => none

def findModule? (name : Name) : CoreM (Option ModuleStatus) := do
  return (← getThe CoreState).modules[name]?

def addModule (name : Name) (status : ModuleStatus) : CoreM Unit := do
  modifyThe CoreState fun st => { st with modules := st.modules.insert name status }

private def checkDuplicateUnivParams (params : List Name) :
    CoreM Unit := do
  let rec loop (seen : Std.HashSet Name) : List Name → CoreM Unit
    | [] => pure ()
    | n :: ns =>
        if n ∈ seen then
          throw (.duplicateUniverseParam n)
        else
          loop (seen.insert n) ns
  loop ∅ params

def elabDefinition (d : Definition) : CoreM Unit := do
  checkDuplicateUnivParams d.univParams
  let metaAction : MetaM (Tm 0 × Ty 0) := do
    let (paramCtx, paramTys) ← withChild 2 (elabParams d.params)
    let (tm, ty) ←
      match d.tyOpt with
      | none =>
          let (tm, tyVal) ← withChild 4 (inferTm d.body paramCtx)
          let ty ← tyVal.quote
          pure (tm, ty)
      | some tyRaw =>
          let ty ← withChild 3 (checkTy tyRaw paramCtx)
          let tyVal ← ty.eval paramCtx.env
          let tm ← withChild 4 (checkTm tyVal d.body paramCtx)
          pure (tm, ty)
    let tm := Tm.lams paramTys tm
    let ty := Ty.pis paramTys ty
    return (tm, ty)
  let mctx : MetaContext := { MetaContext.empty with currentDecl := d.name }
  let some (tm, ty) ← runMetaM metaAction mctx { univParams := d.univParams } | return
  let _ ← Global.addEntry d.name (.definition { univParams := d.univParams, ty, tm })

def elabExample (e : Example) : CoreM Unit := do
  checkDuplicateUnivParams e.univParams
  let metaAction : MetaM Unit := do
    let (paramCtx, _paramTys) ← withChild 0 (elabParams e.params)
    match e.tyOpt with
    | some tyRaw =>
        let expected ← withChild 1 (checkTy tyRaw paramCtx)
        let expected ← expected.eval paramCtx.env
        let _term ← withChild 2 (checkTm expected e.body paramCtx)
    | none =>
        let (_term, _tyVal) ← withChild 2 (inferTm e.body paramCtx)
  let _ ← runMetaM metaAction MetaContext.empty { univParams := e.univParams }

def elabAxiom (a : Axiom) : CoreM Unit := do
  checkDuplicateUnivParams a.univParams
  let metaAction : MetaM Unit := do
    let (paramCtx, paramTys) ← withChild 2 (elabParams a.params)
    let ty ← withChild 3 (checkTy a.ty paramCtx)
    let ty := Ty.pis paramTys ty
    let _ ← Global.addEntry a.name (.axiom { univParams := a.univParams, ty })
  let mctx : MetaContext := { MetaContext.empty with currentDecl := a.name }
  let _ ← runMetaM metaAction mctx { univParams := a.univParams }

def elabInductiveCmd (info : Inductive) : CoreM Unit := do
  checkDuplicateUnivParams info.univParams
  let mctx : MetaContext := { MetaContext.empty with currentDecl := info.name }
  let _ ← runMetaM (elabInductive info) mctx { univParams := info.univParams }

def elabStructureCmd (info : Structure) : CoreM Unit := do
  checkDuplicateUnivParams info.univParams
  let mctx : MetaContext := { MetaContext.empty with currentDecl := info.name }
  let _ ← runMetaM (elabStructure info) mctx { univParams := info.univParams }

end Qdt
