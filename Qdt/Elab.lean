module

public import Qdt.Structure
import Qdt.Bidirectional
import Qdt.HitPrimitive
import Qdt.Params

public section

namespace Qdt

open Lean (Name)
open Frontend (Ast Path)

variable (q₀ : Key)

structure Import where
  moduleName : Name

def Import.parse : Ast → Option Import
  | .node `Command.import cs =>
      if cs.size != 1 then none else
      some { moduleName := cs[0]!.getName }
  | _ => none

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

def Definition.parse : Ast → Option Definition
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

def Example.parse : Ast → Option Example
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

def Axiom.parse : Ast → Option Axiom
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

def checkDuplicateUnivParams (params : List Name) : Option Error :=
  let rec loop (seen : Std.HashSet Name) : List Name → Option Error
    | [] => none
    | n :: ns =>
        if n ∈ seen then
          some (.duplicateUniverseParam n)
        else
          loop (seen.insert n) ns
  loop ∅ params

def Definition.elab (d : Definition) : OptionT (ElabM q₀) Unit := do
  if let some e := checkDuplicateUnivParams d.univParams then
    raiseError q₀ e
  resetMetas q₀
  let (paramCtx, paramTys) ← withChild q₀ 2 (Params.elab q₀ d.params)
  let (tm, ty) ←
    match d.tyOpt with
    | none =>
        let (tm, tyVal) ← withChild q₀ 4 (inferTm q₀ paramCtx d.body)
        let ty ← tyVal.quote q₀
        pure (tm, ty)
    | some tyRaw =>
        let ty ← OptionT.lift (withChild q₀ 3 (checkTy q₀ paramCtx tyRaw))
        let tyVal ← ty.eval q₀ paramCtx.env
        let tm ← OptionT.lift (withChild q₀ 4 (checkTm q₀ paramCtx tyVal d.body))
        pure (tm, ty)
  let _ ← Universe.retryPostponed q₀
  let tm ← tm.zonk q₀
  let ty ← ty.zonk q₀
  let paramTys ← paramTys.mapM (fun (n, t) => return (n, ← t.zonk q₀))
  withChild q₀ 0 (emitHover q₀ (.signature d.name paramTys ty))
  let tm := Tm.lams paramTys tm
  let ty := Ty.pis paramTys ty
  let hadUnsolved ← reportUnsolvedMetas q₀
  if hadUnsolved then
    return
  let userCount := d.univParams.length
  let (promotedNames, subst) :=
    promoteUniverseMVars userCount (ty.freeUMVars ++ tm.freeUMVars)
  let ty := ty.substUMVars subst
  let tm := tm.substUMVars subst
  checkUnusedUniverseParams q₀ d.name d.univParams (ty.usedLevels ++ tm.usedLevels)
  let _ ← addConstant q₀ d.name
    (.definition { numUnivParams := userCount + promotedNames.length, ty, tm })

def Example.elab (e : Example) : OptionT (ElabM q₀) Unit := do
  if let some err := checkDuplicateUnivParams e.univParams then
    raiseError q₀ err
  resetMetas q₀
  let (paramCtx, _paramTys) ← withChild q₀ 0 (Params.elab q₀ e.params)
  match e.tyOpt with
  | some tyRaw =>
      let expected ← OptionT.lift (withChild q₀ 1 (checkTy q₀ paramCtx tyRaw))
      let expected ← expected.eval q₀ paramCtx.env
      let _term ← OptionT.lift (withChild q₀ 2 (checkTm q₀ paramCtx expected e.body))
  | none =>
      let (_term, _tyVal) ← withChild q₀ 2 (inferTm q₀ paramCtx e.body)
  let _ ← Universe.retryPostponed q₀
  let _ ← reportUnsolvedMetas q₀

def Axiom.elab (a : Axiom) : OptionT (ElabM q₀) Unit := do
  if let some err := checkDuplicateUnivParams a.univParams then
    raiseError q₀ err
  resetMetas q₀
  let (paramCtx, paramTys) ← withChild q₀ 2 (Params.elab q₀ a.params)
  let ty ← OptionT.lift (withChild q₀ 3 (checkTy q₀ paramCtx a.ty))
  let _ ← Universe.retryPostponed q₀
  let ty ← ty.zonk q₀
  let paramTys ← paramTys.mapM (fun (n, t) => return (n, ← t.zonk q₀))
  withChild q₀ 0 (emitHover q₀ (.signature a.name paramTys ty))
  let ty := Ty.pis paramTys ty
  let hadUnsolved ← reportUnsolvedMetas q₀
  if hadUnsolved then
    return
  let userCount := a.univParams.length
  let (promotedNames, subst) := promoteUniverseMVars userCount ty.freeUMVars
  let ty := ty.substUMVars subst
  checkUnusedUniverseParams q₀ a.name a.univParams ty.usedLevels
  let numUnivParams := userCount + promotedNames.length
  let entry := (Hit.recogniseAxiom a.name numUnivParams ty).getD
    (.axiom { numUnivParams, ty })
  let _ ← addConstant q₀ a.name entry

def Inductive.elab (info : Inductive) : OptionT (ElabM q₀) Unit := do
  if let some err := checkDuplicateUnivParams info.univParams then
    raiseError q₀ err
  let result ← Inductive.elab' q₀ info
  let userCount := info.univParams.length
  let allConsts := result.indEntry.snd :: result.recEntry.snd ::
    result.ctorEntries.map Prod.snd
  let allMVars := allConsts.flatMap Constant.freeUMVars
  let (promotedNames, subst) := promoteUniverseMVars userCount allMVars
  let promotedCount := promotedNames.length
  let updateConst (c : Constant) : Constant :=
    let c := c.substUMVars subst
    c.setNumUnivParams (c.toConstantInfo.numUnivParams + promotedCount)
  replaceEntry q₀ result.indEntry.fst (updateConst result.indEntry.snd)
  replaceEntry q₀ result.recEntry.fst (updateConst result.recEntry.snd)
  for (cname, cconst) in result.ctorEntries do
    replaceEntry q₀ cname (updateConst cconst)
  let updatedInd := updateConst result.indEntry.snd
  let updatedRec := updateConst result.recEntry.snd
  let ctorUsed := result.ctorEntries.flatMap (fun (_, c) =>
    (updateConst c).ty.usedLevels)
  checkUnusedUniverseParams q₀ info.name info.univParams
    (updatedInd.ty.usedLevels ++ updatedRec.ty.usedLevels ++ ctorUsed)
  let _ ← result.ctorEntries.foldlM (init := 0) fun i (ctorName, ctorConst) => do
    withChild q₀ (4 + i) (emitHover q₀ (.signature ctorName .nil (updateConst ctorConst).ty))
    return i + 1

def Structure.elab (info : Structure) : OptionT (ElabM q₀) Unit := do
  if let some err := checkDuplicateUnivParams info.univParams then
    raiseError q₀ err
  let result ← Structure.elab' q₀ info
  let allConsts := result.indResult.indEntry.snd ::
    result.indResult.recEntry.snd ::
    result.indResult.ctorEntries.map Prod.snd ++ result.projEntries.map Prod.snd
  let used := allConsts.flatMap (fun c => c.ty.usedLevels)
  checkUnusedUniverseParams q₀ info.name info.univParams used

end Qdt
