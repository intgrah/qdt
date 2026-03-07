module

public import Std.Data.HashMap
public import Std.Data.HashSet

public import Qdt.Bidirectional
public import Qdt.Error
public import Qdt.Frontend.Ast
public import Qdt.Theory.Global
public import Qdt.Nbe
public import Qdt.Params
public import Qdt.Quote
public import Qdt.Frontend.Desugar
public import Qdt.Inductive
public import Qdt.Structure

@[expose] public section

namespace Qdt

open Lean (Name)
open Frontend (Ast Path)

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
  | .node `Command.definition cs =>
      if cs.size != 5 then none else
      let name := cs[0]!.getName
      let univParamsAst := cs[1]!
      let paramsAst := cs[2]!
      let tyOpt := cs[3]!
      let body := cs[4]!
      let univParams := match univParamsAst with
        | .node _ cs => cs.toList.filterMap fun c => c.name?
        | _ => []
      let tyOpt : Option Ast :=
        if tyOpt.kind? == some `null || (match tyOpt with | .missing => true | _ => false)
        then none else some tyOpt
      let params := match paramsAst with
        | .node _ cs => cs.toList
        | _ => []
      some { name, univParams, params, tyOpt, body }
  | _ => none

def parseExample : Ast → Option Example
  | .node `Command.example cs =>
      if cs.size != 3 then none else
      let paramsAst := cs[0]!
      let tyOpt := cs[1]!
      let body := cs[2]!
      let tyOpt : Option Ast :=
        if tyOpt.kind? == some `null || (match tyOpt with | .missing => true | _ => false)
        then none else some tyOpt
      let params := match paramsAst with
        | .node _ cs => cs.toList
        | _ => []
      some { univParams := [], params, tyOpt, body }
  | _ => none

def parseAxiom : Ast → Option Axiom
  | .node `Command.axiom cs =>
      if cs.size != 4 then none else
      let name := cs[0]!.getName
      let univParamsAst := cs[1]!
      let paramsAst := cs[2]!
      let ty := cs[3]!
      let univParams := match univParamsAst with
        | .node _ cs => cs.toList.filterMap fun c => c.name?
        | _ => []
      let params := match paramsAst with
        | .node _ cs => cs.toList
        | _ => []
      some { name, univParams, params, ty }
  | _ => none

def parseImport : Ast → Option Import
  | .node `Command.import cs =>
      if cs.size != 1 then none else
      some { moduleName := cs[0]!.getName }
  | _ => none

def checkDuplicateUnivParams (params : List Name) : Option Error :=
  let rec loop (seen : Std.HashSet Name) : List Name → Option Error
    | [] => none
    | n :: ns =>
        if n ∈ seen then
          some (.duplicateUniverseParam n)
        else
          loop (seen.insert n) ns
  loop ∅ params

def elabDefinition (d : Definition) : OptionT MetaM Unit := do
  if let some e := checkDuplicateUnivParams d.univParams then
    raiseError e
  let (paramCtx, paramTys) ← withChild 2 (elabParams d.params)
  let (tm, ty) ←
    match d.tyOpt with
    | none =>
        let (tm, tyVal) ← withChild 4 (inferTm paramCtx d.body)
        let ty ← tyVal.quote
        pure (tm, ty)
    | some tyRaw =>
        let ty ← withChild 3 (checkTy paramCtx tyRaw)
        let tyVal ← ty.eval paramCtx.env
        let tm ← OptionT.lift (withChild 4 (checkTm paramCtx tyVal d.body))
        pure (tm, ty)
  withChild 0 (emitHover (.signature d.name paramTys ty))
  let tm := Tm.lams paramTys tm
  let ty := Ty.pis paramTys ty
  let _ ← addConstant d.name (.definition { univParams := d.univParams, ty, tm })

def elabExample (e : Example) : OptionT MetaM Unit := do
  if let some err := checkDuplicateUnivParams e.univParams then
    raiseError err
  let (paramCtx, _paramTys) ← withChild 0 (elabParams e.params)
  match e.tyOpt with
  | some tyRaw =>
      let expected ← withChild 1 (checkTy paramCtx tyRaw)
      let expected ← expected.eval paramCtx.env
      let _term ← OptionT.lift (withChild 2 (checkTm paramCtx expected e.body))
  | none =>
      let (_term, _tyVal) ← withChild 2 (inferTm paramCtx e.body)

def elabAxiom (a : Axiom) : OptionT MetaM Unit := do
  if let some err := checkDuplicateUnivParams a.univParams then
    raiseError err
  let (paramCtx, paramTys) ← withChild 2 (elabParams a.params)
  let ty ← withChild 3 (checkTy paramCtx a.ty)
  withChild 0 (emitHover (.signature a.name paramTys ty))
  let ty := Ty.pis paramTys ty
  let _ ← addConstant a.name (.axiom { univParams := a.univParams, ty })

def elabInductiveCmd (info : Inductive) : OptionT MetaM Unit := do
  if let some err := checkDuplicateUnivParams info.univParams then
    raiseError err
  let result ← elabInductive info
  let _ ← result.ctorEntries.foldlM (init := 0) fun i (ctorName, ctorConst) => do
    withChild (4 + i) (emitHover (.signature ctorName .nil ctorConst.ty))
    return i + 1

def elabStructureCmd (info : Structure) : OptionT MetaM Unit := do
  if let some err := checkDuplicateUnivParams info.univParams then
    raiseError err
  let _ ← elabStructure info

end Qdt
