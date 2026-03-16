module

public import Qdt.Theory.Substitution.Basic
public import Qdt.Params

public section

namespace Qdt

open Lean (Name)

open Frontend (Ast Path)

variable (ι₀ : ∀ i, InputV i) (q₀ : Key)

public structure InductiveConstructor where
  name : Name
  fields : List Ast
  tyOpt : Option Ast
deriving Inhabited

public structure Inductive where
  name : Name
  recName : Name
  univParams : List Name
  params : List Ast
  tyOpt : Option Ast
  ctors : List InductiveConstructor

def InductiveConstructor.parse  : Ast → Option InductiveConstructor
  | .node `Constructor cs =>
      let name := cs[0]!.getName
      let fieldsNode := cs[1]!
      let tyOpt := cs[2]!
      let fields := match fieldsNode with
        | .node _ cs => cs.toList
        | _ => []
      let tyOpt : Option Ast := match tyOpt with
        | .node `null _ | .missing => none
        | _ => some tyOpt
      some { name, fields, tyOpt }
  | _ => none

public def Inductive.parse : Ast → Option Inductive
  | .node `Command.inductive cs =>
      let name := cs[0]!.getName
      let univParamsNode := cs[1]!
      let paramsNode := cs[2]!
      let tyOpt := cs[3]!
      let ctorsNode := cs[4]!
      let univParams := match univParamsNode with
        | .node _ cs => cs.toList.filterMap fun c => c.name?
        | _ => []
      let params := match paramsNode with
        | .node _ cs => cs.toList
        | _ => []
      let tyOpt : Option Ast := match tyOpt with
        | .node `null _ | .missing => none
        | _ => some tyOpt
      let ctors := match ctorsNode with
        | .node _ cs => cs.toList.filterMap InductiveConstructor.parse
        | _ => []
      some { name, recName := name.str "rec", univParams, params, tyOpt, ctors }
  | _ => none

def Tm.getAppArgs {n : Nat} : Tm n → Tm n × List (Tm n) :=
  go []
  where
  go {n : Nat} (spine : List (Tm n)) : Tm n → Tm n × List (Tm n)
    | .app f a => go (a :: spine) f
    | t => (t, spine)

def Ty.getTele {a : Nat} : Ty a → Σ b, Ctx a b × Ty b :=
  go Tele.nil
  where
  go {a b : Nat}
      (acc : Ctx a b) :
      Ty b →
      Σ nb : Nat, Ctx a nb × Ty nb
    | .pi name ty b => go (acc.snoc (name, ty)) b
    | t => ⟨b, acc, t⟩

unsafe def weaken_impl {n m : Nat} : List (VTm n) → (_ : n ≤ m) → List (VTm m) := unsafeCast

def weaken' {n m : Nat} (ts : List (VTm n)) (h : n ≤ m) : List (VTm m) :=
  ts.map (VTm.weaken h)

public def weaken {n m : Nat} (ts : List (VTm n)) (h : n ≤ m := by omega) : List (VTm m) := weaken' ts h

def Env.infer : {n : Nat} → Env n n
  | 0 => Env.nil
  | n + 1 => Env.infer.weaken.cons (VTm.varAt n)

mutual

def Tm.hasIndOcc {n : Nat} (ind : Name) : Tm n → Bool
  | .u' _ => false
  | .var _ => false
  | .const name _ => name == ind
  | .lam _ a b => a.hasIndOcc ind || b.hasIndOcc ind
  | .app a b => a.hasIndOcc ind || b.hasIndOcc ind
  | .pi' _ a b => a.hasIndOcc ind || b.hasIndOcc ind
  | .proj _ a => a.hasIndOcc ind
  | .letE _ a b c => a.hasIndOcc ind || b.hasIndOcc ind || c.hasIndOcc ind

def Ty.hasIndOcc {n : Nat} (ind : Name) : Ty n → Bool
  | .u _ => false
  | .pi _ a b => a.hasIndOcc ind || b.hasIndOcc ind
  | .el a => a.hasIndOcc ind

end

structure RecFieldInfo (n : Nat) where
  nestedEnd : Nat
  nestedTele : Ctx n nestedEnd
  indices : List (Tm nestedEnd)

structure ParamRec (n : Nat) where
  name : Name
  ty : Ty n
  recOpt : Option (RecFieldInfo n)

structure RecFieldSeed (numParamsMotivesMinors numFields : Nat) where
  fieldIdx : Fin numFields
  nestedEnd : Nat
  nestedTele : Ctx (numParamsMotivesMinors + numFields) nestedEnd
  indices : List (Tm nestedEnd)

structure RuleSeed (numParamsMotivesMinors : Nat) where
  ctorName : Name
  numFields : Nat
  recFields : List (RecFieldSeed numParamsMotivesMinors numFields)

def Ctx.shiftAt {a b : Nat} (cutoff s : Nat) (tele : Ctx a b) : Ctx (a + s) (b + s) :=
  tele.dmap s fun {n : Nat} ⟨name, ty⟩ => ⟨name, ty.shiftAfter (n + cutoff) s⟩

def Ctx.shift {m k : Nat} := @Ctx.shiftAt m k 0

def indConsistency {n : Nat}
    (numParams numIndices : Nat)
    (indName ctorName : Name)
    (args : List (Tm n)) :
    OptionT (ElabM ι₀ q₀) (List (Tm n)) := do
  if args.length != numParams + numIndices then
    raiseError ι₀ q₀ (.nonPositiveOccurrence indName)
  let (params, indices) := args.splitAt numParams
  for (ithParam, param) in params.mapIdx Prod.mk do
    let .var j := param
      | raiseError ι₀ q₀ (.ctorParamMismatch ctorName)
    if ithParam + j.val + 1 != n then
      raiseError ι₀ q₀ (.ctorParamMismatch ctorName)
  for index in indices do
    if index.hasIndOcc indName then
      raiseError ι₀ q₀ (.nonPositiveOccurrence indName)
  return indices

def analyseRecField
    (numParams numIndices : Nat)
    (indName ctorName : Name)
    (jthFieldCtx : Nat)
    (fty : Ty jthFieldCtx) :
    OptionT (ElabM ι₀ q₀) (Option (RecFieldInfo jthFieldCtx)) := do
  let ⟨nb, nestedTele, endTy⟩ := fty.getTele
  if nestedTele.any (fun ⟨_, t⟩ => t.hasIndOcc indName) then
    raiseError ι₀ q₀ (.nonPositiveOccurrence indName)
  match endTy with
  | .u _ => return none
  | .el tm => do
      let (head, args) := tm.getAppArgs
      if let .const name _ := head then
        if name == indName then
          let indices ← indConsistency ι₀ q₀ numParams numIndices indName ctorName args
          return some { nestedEnd := nb, nestedTele, indices : RecFieldInfo _ }
        else
          for arg in args do
            if arg.hasIndOcc indName then
              raiseError ι₀ q₀ (.nonPositiveOccurrence indName)
          return none
      else
        if tm.hasIndOcc indName then
          raiseError ι₀ q₀ (.nonPositiveOccurrence indName)
        return none
  | .pi .. => raiseError ι₀ q₀ (.msg "Internal error")

def getTypedBinder' : Ast → Option (Name × Ast)
  | .node `Binder.typed cs => some (cs[0]!.getName, cs[1]!)
  | _ => none

def getFieldName' : Ast → Option Name
  | .node _ cs => cs[0]!.name?
  | _ => none

def InductiveConstructor.elab {numParams}
    (numIndices : Nat)
    (indName : Name)
    (indUnivs : List Universe)
    (indTyVal : VTy numParams)
    (resultUniv : Universe)
    (paramCtx : TermContext numParams)
    (ctor : InductiveConstructor) :
    OptionT (ElabM ι₀ q₀) (Name × Ty numParams) := do
  if !ctor.name.isAtomic then
    raiseError ι₀ q₀ (.ctorNameNotAtomic ctor.name)
  let ctorName := indName.append ctor.name
  let indParamCtx : TermContext (numParams + 1) := paramCtx.bind indName indTyVal
  let params : List (VTm (numParams + 1)) := List.finRange numParams |>.map fun i => VTm.varAt i.val
  let (fieldCtx, fieldTys, fieldUnivs) ← withChild ι₀ q₀ 1 (Params.elabWithLevels ι₀ q₀ indParamCtx ctor.fields)
  for (field, fieldUniv) in ctor.fields.zip fieldUnivs do
    let fieldName := getFieldName' field |>.getD .anonymous
    if !Universe.le fieldUniv resultUniv then
      raiseError ι₀ q₀ (.fieldUniverseTooLarge ctorName fieldName fieldUniv resultUniv)
  let numFields := ctor.fields.length
  let retTy ←
    match ctor.tyOpt with
    | some retTyAst =>
      OptionT.lift (withChild ι₀ q₀ 2 (checkTy ι₀ q₀ fieldCtx retTyAst))
    | none => do
        if numIndices > 0 then
          raiseError ι₀ q₀ (Error.typeFamilyCtorReturnTypeRequired ctorName)
        let indVar : VTm (numParams + 1 + numFields) := VTm.varAt numParams
        let res ← indVar.apps ι₀ q₀ (weaken params)
        let res ← res.quote ι₀ q₀
        pure (Ty.el res)
  let ctorTyWithInd : Ty (numParams + 1) := Ty.pis fieldTys retTy
  let ctorTy : Ty numParams := ctorTyWithInd.subst (Subst.beta (.const indName indUnivs))
  return (ctorName, ctorTy)

public structure InductiveResult where
  indEntry : Name × Constant
  ctorEntries : List (Name × Constant)
  recEntry : Name × Constant

def shiftIndexTys {a k : Nat} (s : Nat) : Ctx a k → Ctx (a + s) (k + s)
  | .nil => Tele.nil
  | .snoc (b := n) bs ⟨name, ty⟩ =>
      have : n + s + 1 = n + 1 + s := by omega
      this ▸ (shiftIndexTys s bs).snoc ⟨name, ty.shiftAfter (n - a) s⟩

@[specialize]
def buildIhs
    {numParamsMotives numMinors ithMinor}
    (numParamsMotivesIthMinorFields numFields : Nat)
    (motiveVal : VTm numParamsMotives)
    (him : ithMinor ≤ numMinors)
    (hle : numParamsMotives + ithMinor + numFields = numParamsMotivesIthMinorFields)
    {j k : Nat}
    (hj : j ≤ numParamsMotivesIthMinorFields)
    (ihTele : Ctx numParamsMotivesIthMinorFields k)
    (recFields : List (RecFieldSeed (numParamsMotives + numMinors) numFields)) :
    Tele ParamRec (numParamsMotives + ithMinor) j →
    ElabM ι₀ q₀ (Σ nRec : Nat, Ctx numParamsMotivesIthMinorFields nRec × List (RecFieldSeed (numParamsMotives + numMinors) numFields))
  | .nil => return ⟨k, ihTele, recFields⟩
  | .snoc (b := idx) fs f => do
      have hIdx : idx < numParamsMotivesIthMinorFields := by omega
      let ⟨k, ihTele, recFields⟩ ←
        buildIhs numParamsMotivesIthMinorFields numFields motiveVal him hle (hj := Nat.le_of_lt hIdx) ihTele recFields fs
      let some info := f.recOpt
        | return ⟨k, ihTele, recFields⟩
      have : idx ≤ info.nestedEnd := info.nestedTele.le
      let numNested : Nat := info.nestedEnd - idx
      let fieldsAfter : Nat := numParamsMotivesIthMinorFields - idx
      let numParamsMotivesMinors := numParamsMotives + numMinors
      let numParamsMotivesIthMinor := numParamsMotives + ithMinor

      have hStart : idx + fieldsAfter = numParamsMotivesIthMinorFields := by omega
      let nestedEnd₁ : Nat := numParamsMotivesIthMinorFields + numNested
      have hEnd : info.nestedEnd + fieldsAfter = nestedEnd₁ := by omega
      let nestedTele₁ : Ctx numParamsMotivesIthMinorFields nestedEnd₁ :=
        hEnd ▸ hStart ▸ info.nestedTele.dmap fieldsAfter fun {n : Nat} ⟨name, ty⟩ =>
          ⟨name, ty.shiftAfter (n - idx) fieldsAfter⟩
      let indices₁ : List (Tm nestedEnd₁) :=
        info.indices.map (hEnd ▸ ·.shiftAfter numNested fieldsAfter)

      let indices₁ ← indices₁.mapM (fun t => (t.eval ι₀ q₀ Env.infer))

      let fieldVar : VTm nestedEnd₁ := VTm.varAt idx
      let nestedArgs : List (VTm nestedEnd₁) :=
        List.finRange numNested |>.map fun j => VTm.varAt (numParamsMotivesIthMinorFields + j.val)
      let recVal ← fieldVar.apps ι₀ q₀ nestedArgs

      let ih : VTm nestedEnd₁ := motiveVal.weaken
      let ih ← ih.apps ι₀ q₀ indices₁
      let ih ← ih.app ι₀ q₀ recVal
      let ih ← ih.quote ι₀ q₀
      let ih := Ty.el ih
      let ih := Ty.pis nestedTele₁ ih

      let ihName := f.name.str "ih"
      let numIhsSoFar := k - numParamsMotivesIthMinorFields
      have hShift : numParamsMotivesIthMinorFields + numIhsSoFar = k := by
        have : numParamsMotivesIthMinorFields ≤ k := ihTele.le
        omega
      let ihTy : Ty k := hShift ▸ ih.shift numIhsSoFar
      let ihTele := ihTele.snoc ⟨ihName, ihTy⟩

      let minorsAfter : Nat := numMinors - ithMinor
      let rhsCtx := numParamsMotivesMinors + numFields
      let nestedEnd₂ : Nat := rhsCtx + numNested
      have hStart₂ : idx + minorsAfter + fieldsAfter = rhsCtx := by omega
      have hEnd₂ : info.nestedEnd + minorsAfter + fieldsAfter = nestedEnd₂ := by omega
      let numParamsMotivesIthMinor := numParamsMotives + ithMinor
      have hAssoc1 : idx + (minorsAfter + fieldsAfter) = idx + minorsAfter + fieldsAfter := by omega
      have hAssoc2 : info.nestedEnd + (minorsAfter + fieldsAfter) = info.nestedEnd + minorsAfter + fieldsAfter := Nat.add_assoc _ _ _ |>.symm
      let nestedTele₂ : Ctx rhsCtx nestedEnd₂ :=
        hEnd₂ ▸ hStart₂ ▸ hAssoc1 ▸ hAssoc2 ▸ info.nestedTele.dmap (minorsAfter + fieldsAfter) fun {n : Nat} ⟨name, ty⟩ =>
          let ty := ty.shiftAfter (n - idx) fieldsAfter
          have : n + fieldsAfter + minorsAfter = n + (minorsAfter + fieldsAfter) := by omega
          ⟨name, this ▸ ty.shiftAfter (n - numParamsMotivesIthMinor + fieldsAfter) minorsAfter⟩

      let indices₂ : List (Tm nestedEnd₂) :=
        info.indices.map fun t =>
          let numNested := info.nestedEnd - idx
          let t := t.shiftAfter numNested fieldsAfter
          have : info.nestedEnd + fieldsAfter + minorsAfter = info.nestedEnd + minorsAfter + fieldsAfter := by omega
          let t : Tm (info.nestedEnd + minorsAfter + fieldsAfter) := this ▸ t.shiftAfter (info.nestedEnd - numParamsMotivesIthMinor + fieldsAfter) minorsAfter
          hEnd₂ ▸ t

      let fieldIdx : Fin numFields := ⟨idx - numParamsMotivesIthMinor, by have := fs.le; omega⟩
      let recFields := recFields ++ [{ fieldIdx, nestedEnd := nestedEnd₂, nestedTele := nestedTele₂, indices := indices₂ }]
      return ⟨k + 1, ihTele, recFields⟩

@[specialize]
def buildMinorTy
    (numParams numIndices numMinors : Nat)
    (indName : Name)
    (indUnivs : List Universe)
    (motiveVal : VTm (numParams + 1))
    (params : List (VTm numParams))
    (ctorName : Name)
    (ithMinor : Nat)
    (him : ithMinor ≤ numMinors)
    (ctorFieldsTy : Ty numParams) :
    OptionT (ElabM ι₀ q₀) ((Name × Ty (numParams + 1 + ithMinor)) × RuleSeed (numParams + 1 + numMinors)) := do
  let numParamsMotivesIthMinor : Nat := numParams + 1 + ithMinor
  let numParamsMotivesMinors := numParams + 1 + numMinors
  let ctorFieldsTy ← ctorFieldsTy.eval ι₀ q₀ Env.infer
  let ctorFieldsTy : VTy numParamsMotivesIthMinor := ctorFieldsTy.weaken
  let ctorFieldsTy : Ty numParamsMotivesIthMinor ← ctorFieldsTy.quote ι₀ q₀
  let ⟨numParamsMotivesIthMinorFields, fieldTele, ctorRetTy⟩ := ctorFieldsTy.getTele
  let numFields := numParamsMotivesIthMinorFields - numParamsMotivesIthMinor

  let fieldTeleRec : Tele ParamRec numParamsMotivesIthMinor numParamsMotivesIthMinorFields ←
    fieldTele.mapM fun {jf} ⟨name, ty⟩ => do
      let recOpt ← analyseRecField ι₀ q₀ numParams numIndices indName ctorName jf ty
      return ⟨name, ty, recOpt⟩

  have : numParamsMotivesIthMinor ≤ numParamsMotivesIthMinorFields := fieldTele.le

  let ⟨ihEnd, ihTele, recFields⟩ ←
    buildIhs ι₀ q₀ numParamsMotivesIthMinorFields numFields
      motiveVal him (by omega) (hj := Nat.le_refl _) .nil [] fieldTeleRec

  let resultCtx : Nat := ihEnd

  have := ihTele.le
  let fieldsVars : List (VTm resultCtx) :=
    List.finRange numFields |>.map fun i => VTm.varAt (numParamsMotivesIthMinor + i.val)

  let ctorApp : VTm resultCtx := VTm.const ctorName indUnivs
  let ctorApp ← ctorApp.apps ι₀ q₀ (weaken params)
  let ctorApp ← ctorApp.apps ι₀ q₀ fieldsVars

  let ctorIdxVals ←
    match ctorRetTy with
    | .el tm =>
        let (head, args) := tm.getAppArgs
        let .const name _ := head
          | raiseError ι₀ q₀ (Error.ctorMustReturnInductive ctorName indName)
        if name != indName then
          raiseError ι₀ q₀ (Error.ctorMustReturnInductive ctorName indName)
        indConsistency ι₀ q₀ numParams numIndices indName ctorName args
    | .u _ => raiseError ι₀ q₀ (Error.ctorMustReturnInductive ctorName indName)
    | .pi .. => raiseError ι₀ q₀ (.msg "Internal error")
  let ctorIdxVals ← ctorIdxVals.mapM (fun t => (t.eval ι₀ q₀ Env.infer))
  let ctorIdxVals := ctorIdxVals.map VTm.weaken

  let minorTy : VTm resultCtx := motiveVal.weaken
  let minorTy ← minorTy.apps ι₀ q₀ ctorIdxVals
  let minorTy ← minorTy.app ι₀ q₀ ctorApp
  let minorTy ← minorTy.quote ι₀ q₀
  let minorTy := Ty.el minorTy
  let minorTy := Ty.pis ihTele minorTy
  let minorTy := Ty.pis fieldTele minorTy

  return (⟨ctorName, minorTy⟩, ⟨ctorName, numFields, recFields⟩)

@[specialize]
def buildRecRule {numParams numMinors}
    (motiveVal : VTm (numParams + 1))
    (motiveUnivName : Name)
    (indUnivs : List Universe)
    (recName : Name)
    (params : List (VTm numParams))
    (i : Fin numMinors)
    (seed : RuleSeed (numParams + 1 + numMinors)) :
    OptionT (ElabM ι₀ q₀) (RecursorRule (numParams + 1 + numMinors)) := do
  let numParamsMotives := numParams + 1
  let numParamsMotivesMinors := numParamsMotives + numMinors
  let numFields := seed.numFields
  let numParamsMotivesMinorsFields : Nat := numParamsMotivesMinors + numFields

  let ihVals ← seed.recFields.mapM fun rf => do
    let numParamsMotivesMinorsFieldsNested : Nat := rf.nestedEnd
    let numNested : Nat := rf.nestedEnd - numParamsMotivesMinorsFields

    have : numParamsMotivesMinorsFields ≤ numParamsMotivesMinorsFieldsNested := rf.nestedTele.le
    let minors : List (VTm numParamsMotivesMinorsFieldsNested) :=
      List.finRange numMinors |>.map fun ithMinor => VTm.varAt (numParamsMotives + ithMinor.val)

    let indices ← rf.indices.mapM (fun t => (t.eval ι₀ q₀ Env.infer))

    let nestedArgs : List (VTm numParamsMotivesMinorsFieldsNested) :=
      List.finRange numNested |>.map fun j => VTm.varAt (numParamsMotivesMinorsFields + j.val)

    let majorArg : VTm numParamsMotivesMinorsFieldsNested := VTm.varAt (numParamsMotivesMinors + rf.fieldIdx.val)
    let majorArg ← majorArg.apps ι₀ q₀ nestedArgs

    let recUnivs := .level motiveUnivName :: indUnivs
    let recVal : VTm numParamsMotivesMinorsFieldsNested := VTm.const recName recUnivs
    let recVal ← recVal.apps ι₀ q₀ (weaken params (by omega))
    let recVal ← recVal.app ι₀ q₀ (motiveVal.weaken (by omega))
    let recVal ← recVal.apps ι₀ q₀ minors
    let recVal ← recVal.apps ι₀ q₀ indices
    let recVal ← recVal.app ι₀ q₀ majorArg
    let recVal ← recVal.quote ι₀ q₀
    let recVal := Tm.lams rf.nestedTele recVal
    (recVal.eval ι₀ q₀ Env.infer)

  let fieldsVals : List (VTm numParamsMotivesMinorsFields) :=
    List.finRange numFields |>.map fun j => VTm.varAt (numParamsMotivesMinors + j.val)

  let rhsVal : VTm numParamsMotivesMinorsFields := VTm.varAt (numParamsMotives + i.val)
  let rhsVal ← rhsVal.apps ι₀ q₀ fieldsVals
  let rhsVal ← rhsVal.apps ι₀ q₀ ihVals
  let rhsVal ← rhsVal.quote ι₀ q₀

  return {
    ctorName := seed.ctorName,
    numFields := numFields,
    rhs := rhsVal,
    : RecursorRule numParamsMotivesMinors
  }

@[specialize]
def goMinors
    (numParams numIndices numMinors : Nat)
    (indName : Name)
    (indUnivs : List Universe)
    (motiveVal : VTm (numParams + 1))
    (params : List (VTm numParams))
    (ctors : Vector (Name × Ty numParams) numMinors)
    (ithMinor : Nat)
    (hi : ithMinor ≤ numMinors)
    (acc : Ctx (numParams + 1) (numParams + 1 + ithMinor))
    (seeds : Vector (RuleSeed (numParams + 1 + numMinors)) ithMinor) :
    OptionT (ElabM ι₀ q₀) (Ctx (numParams + 1) (numParams + 1 + numMinors) × Vector (RuleSeed (numParams + 1 + numMinors)) numMinors) := do
  if h' : ithMinor < numMinors then
    let (ctorName, ctorFieldsTy) := ctors[ithMinor]
    let (p, seed) ←
      buildMinorTy ι₀ q₀ numParams numIndices numMinors
        indName indUnivs motiveVal params ctorName ithMinor (Nat.le_of_lt h') ctorFieldsTy
    let acc := acc.snoc p
    goMinors numParams numIndices numMinors
      indName indUnivs motiveVal params ctors
      (ithMinor + 1) (by omega) acc (seeds.push seed)
  else
    have hEq : ithMinor = numMinors := by omega
    have hk : numParams + 1 + ithMinor = numParams + 1 + numMinors := by omega
    return (hk ▸ acc, hEq ▸ seeds)

public def Inductive.elab' (ind : Inductive) : OptionT (ElabM ι₀ q₀) InductiveResult := do
  let numParams := ind.params.length
  let numMotives := 1
  let numParamsMotives := numParams + numMotives
  let (paramCtx, paramTys) ← withChild ι₀ q₀ 2 (Params.elab ι₀ q₀ ind.params)
  let params := List.finRange numParams |>.map VTm.var
  let resultTy : Ty numParams ←
    match ind.tyOpt with
    | none => pure (Ty.u .zero)
    | some ty => OptionT.lift (withChild ι₀ q₀ 3 (checkTy ι₀ q₀ paramCtx ty))
  withChild ι₀ q₀ 0 (emitHover ι₀ q₀ (.signature ind.name paramTys resultTy))
  let indTy : Ty 0 := Ty.pis paramTys resultTy
  let univParams ← getUnivParams ι₀ q₀

  let _ ← addConstant ι₀ q₀ ind.name (.opaque { univParams, ty := indTy })

  let ⟨numParamsIndices, indexTys, returnTy⟩ := resultTy.getTele
  let numIndices := numParamsIndices - numParams
  let resultUniv ← match returnTy with
    | .u u => pure u
    | .el _ => raiseError ι₀ q₀ (.inductiveReturnTypeMustBeTypeUniverse ind.name)
    | .pi _ _ _ => raiseError ι₀ q₀ (.msg "internal error")

  let indUnivs := univParams.map Universe.level
  let indVal : VTm 0 := VTm.const ind.name indUnivs

  let motiveIndices : List (VTm numParamsIndices) :=
    List.finRange numIndices |>.map fun i => VTm.varAt (numParams + i.val)

  let motiveInd : VTm numParamsIndices := indVal.weaken
  let motiveInd ← motiveInd.apps ι₀ q₀ (weaken params indexTys.le)
  let motiveInd ← motiveInd.apps ι₀ q₀ motiveIndices
  let motiveInd ← motiveInd.quote ι₀ q₀

  let motiveUnivName := Universe.freshName univParams
  let motiveTy : Ty numParams :=
    Ty.pis indexTys <|
    Ty.arrow (Ty.el motiveInd) <|
    Ty.u (.level motiveUnivName)
  let motiveVal : VTm numParamsMotives := VTm.varAt numParams

  let numMinors := ind.ctors.length
  let indTyVal : VTy 0 ← indTy.eval ι₀ q₀ .nil
  let indTyVal : VTy numParams := indTyVal.weaken
  let ctors ← (Vector.finRange numMinors).mapM fun i =>
    withChild ι₀ q₀ (4 + i.val) <|
      (ind.ctors.get ⟨i.val, i.isLt⟩).elab ι₀ q₀
        numIndices ind.name indUnivs indTyVal resultUniv paramCtx

  let ctorEntries : List (Name × Constant) := ctors.toList.map fun (name, ctorFieldsTy) =>
    let ctorFieldsTy := Ty.pis paramTys ctorFieldsTy
    (name, .constructor { univParams, ty := ctorFieldsTy, indName := ind.name })

  for (name, entry) in ctorEntries do
    let _ ← addConstant ι₀ q₀ name entry

  let numParamsMotivesMinors := numParamsMotives + numMinors

  let ctorNames := ctors.map Prod.fst

  let indInfo : InductiveInfo := {
    univParams
    ty := indTy
    numParams
    numIndices
    numMinors
    ctorNames
  }
  let indEntry : Name × Constant := (ind.name, .inductive indInfo)

  let recName := ind.recName

  let (minorTys, seeds) ←
    goMinors ι₀ q₀ numParams numIndices numMinors ind.name indUnivs motiveVal params ctors 0 (Nat.zero_le numMinors) .nil ⟨#[], rfl⟩

  let numParamsMotivesMinorsIndices := numParamsMotivesMinors + numIndices
  let indexTys' : Ctx numParamsMotivesMinors numParamsMotivesMinorsIndices :=
    have h1 : numParams + (1 + numMinors) = numParamsMotivesMinors := by omega
    have h2 : numParamsIndices + (1 + numMinors) = numParamsMotivesMinorsIndices := by have := indexTys.le; omega
    h2 ▸ h1 ▸ shiftIndexTys (1 + numMinors) indexTys

  let recRules ← Vector.finRange numMinors
    |>.zip seeds
    |>.mapM fun (i, seed) =>
    buildRecRule ι₀ q₀ motiveVal motiveUnivName indUnivs recName params i seed

  let indicesVals : List (VTm numParamsMotivesMinorsIndices) :=
    List.finRange numIndices |>.map fun j => VTm.varAt (numParamsMotivesMinors + j.val)

  let majorTy : VTm numParamsMotivesMinorsIndices := indVal.weaken
  let majorTy ← majorTy.apps ι₀ q₀ (weaken params)
  let majorTy ← majorTy.apps ι₀ q₀ indicesVals
  let majorTy ← majorTy.quote ι₀ q₀
  let majorTy := Ty.el majorTy
  let majorVal : VTm (numParamsMotivesMinorsIndices + 1) := VTm.varAt numParamsMotivesMinorsIndices

  let conclusionTy : VTm (numParamsMotivesMinorsIndices + 1) := motiveVal.weaken
  let conclusionTy ← conclusionTy.apps ι₀ q₀ (weaken indicesVals)
  let conclusionTy ← conclusionTy.app ι₀ q₀ majorVal
  let conclusionTy ← conclusionTy.quote ι₀ q₀
  let conclusionTy := Ty.el conclusionTy

  let recTy : Ty 0 :=
    Ty.pis paramTys <|
    Ty.pi `motive motiveTy <|
    Ty.pis minorTys <|
    Ty.pis indexTys' <|
    Ty.arrow majorTy <|
    conclusionTy

  let recUnivParams := motiveUnivName :: univParams
  let recInfo : RecursorInfo := {
    univParams := recUnivParams
    ty := recTy
    recName
    numParams
    numMotives := 1
    numMinors
    numIndices
    recRules
  }
  let recEntry : Name × Constant := (recName, .recursor recInfo)

  let _ ← addConstant ι₀ q₀ recName recEntry.2
  replaceEntry ι₀ q₀ ind.name indEntry.2

  return { indEntry, ctorEntries, recEntry }

end Qdt
