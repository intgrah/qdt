module

public import Qdt.MLTT.Context
public import Qdt.MLTT.Substitution.Basic
public import Qdt.Control
public import Qdt.Frontend.Ast
public import Qdt.Params
public import Qdt.Nbe
public import Qdt.Quote

@[expose] public section

namespace Qdt

export Lean (Name)

open Frontend (Ast Path)

structure InductiveConstructor where
  name : Name
  fields : List Ast
  tyOpt : Option Ast
deriving Inhabited

structure Inductive where
  name : Name
  univParams : List Name
  params : List Ast
  tyOpt : Option Ast
  ctors : List InductiveConstructor

def parseConstructor  : Ast → Option InductiveConstructor
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

def parseInductive : Ast → Option Inductive
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
        | .node _ cs => cs.toList.filterMap fun c => parseConstructor c
        | _ => []
      some { name, univParams, params, tyOpt, ctors }
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
    | .pi param b => go (acc.snoc param) b
    | t => ⟨b, acc, t⟩

unsafe def weaken_impl {n m : Nat} : List (VTm n) → (_ : n ≤ m) → List (VTm m) := unsafeCast

def weaken' {n m : Nat} (ts : List (VTm n)) (h : n ≤ m) : List (VTm m) :=
  ts.map (VTm.weaken h)

def weaken {n m : Nat} (ts : List (VTm n)) (h : n ≤ m := by omega) : List (VTm m) := weaken' ts h

def Env.infer : {n : Nat} → Env n n
  | 0 => Env.nil
  | n + 1 => Env.infer.weaken.cons (VTm.varAt n)

mutual

def Tm.hasIndOcc {n : Nat} (ind : Name) : Tm n → Bool
  | .u' _ => false
  | .var _ => false
  | .const name _ => name == ind
  | .lam ⟨_, a⟩ b => a.hasIndOcc ind || b.hasIndOcc ind
  | .app a b => a.hasIndOcc ind || b.hasIndOcc ind
  | .pi' ⟨_, a⟩ b => a.hasIndOcc ind || b.hasIndOcc ind
  | .proj _ a => a.hasIndOcc ind
  | .letE _ a b c => a.hasIndOcc ind || b.hasIndOcc ind || c.hasIndOcc ind

def Ty.hasIndOcc {n : Nat} (ind : Name) : Ty n → Bool
  | .u _ => false
  | .pi ⟨_, a⟩ b => a.hasIndOcc ind || b.hasIndOcc ind
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
    OptionT MetaM (List (Tm n)) := do
  if args.length != numParams + numIndices then
    raiseError (.nonPositiveOccurrence indName)
  let (params, indices) := args.splitAt numParams
  for (ithParam, param) in params.mapIdx Prod.mk do
    let .var j := param
      | raiseError (.ctorParamMismatch ctorName)
    if ithParam + j.val + 1 != n then
      raiseError (.ctorParamMismatch ctorName)
  for index in indices do
    if index.hasIndOcc indName then
      raiseError (.nonPositiveOccurrence indName)
  return indices

def analyseRecField
    (numParams numIndices : Nat)
    (indName ctorName : Name)
    (jthFieldCtx : Nat)
    (fty : Ty jthFieldCtx) :
    OptionT MetaM (Option (RecFieldInfo jthFieldCtx)) := do
  let ⟨nb, nestedTele, endTy⟩ := fty.getTele
  if nestedTele.any (fun ⟨_, t⟩ => t.hasIndOcc indName) then
    raiseError (.nonPositiveOccurrence indName)
  match endTy with
  | .u _ => return none
  | .el tm => do
      let (head, args) := tm.getAppArgs
      if let .const name _ := head then
        if name == indName then
          let indices ← indConsistency numParams numIndices indName ctorName args
          return some { nestedEnd := nb, nestedTele, indices : RecFieldInfo _ }
        else
          for arg in args do
            if arg.hasIndOcc indName then
              raiseError (.nonPositiveOccurrence indName)
          return none
      else
        if tm.hasIndOcc indName then
          raiseError (.nonPositiveOccurrence indName)
        return none
  | .pi .. => raiseError (.msg "Internal error")

def getTypedBinder' : Ast → Option (Name × Ast)
  | .node `Binder.typed cs => some (cs[0]!.getName, cs[1]!)
  | _ => none

def getFieldName' : Ast → Option Name
  | .node _ cs => cs[0]!.name?
  | _ => none

def elabCtor
    (numParams numIndices : Nat)
    (indName : Name)
    (indUnivs : List Universe)
    (indTyVal : VTy numParams)
    (resultUniv : Universe)
    (paramCtx : TermContext numParams)
    (ctor : InductiveConstructor) :
    OptionT MetaM (Name × Ty numParams) := do
  if !ctor.name.isAtomic then
    raiseError (.msg s!"{ctor.name}: constructor name must be atomic")
  let ctorName := indName.append ctor.name
  let indParamCtx : TermContext (numParams + 1) := paramCtx.bind indName indTyVal
  let params : List (VTm (numParams + 1)) := List.finRange numParams |>.map fun i => VTm.varAt i.val
  let (fieldCtx, fieldTys, fieldUnivs) ← withChild 1 (elabParamsWithLevels indParamCtx ctor.fields)
  for (field, fieldUniv) in ctor.fields.zip fieldUnivs do
    let fieldName := getFieldName' field |>.getD .anonymous
    if !Universe.le fieldUniv resultUniv then
      raiseError (.fieldUniverseTooLarge ctorName fieldName fieldUniv resultUniv)
  let numFields := ctor.fields.length
  let retTy ←
    match ctor.tyOpt with
    | some retTyAst =>
      withChild 2 (checkTy fieldCtx retTyAst)
    | none => do
        if numIndices > 0 then
          raiseError (Error.typeFamilyCtorReturnTypeRequired ctorName)
        let indVar : VTm (numParams + 1 + numFields) := VTm.varAt numParams
        let res ← indVar.apps (weaken params)
        let res ← res.quote
        pure (Ty.el res)
  let ctorTyWithInd : Ty (numParams + 1) := Ty.pis fieldTys retTy
  let ctorTy : Ty numParams := ctorTyWithInd.subst (Subst.beta (.const indName indUnivs))
  return (ctorName, ctorTy)

structure InductiveResult where
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
    (numParamsMotives numMinors ithMinor : Nat)
    (motiveVal : VTm numParamsMotives)
    (numParamsMotivesIthMinorFields numFields : Nat)
    (him : ithMinor ≤ numMinors)
    (hle : numParamsMotives + ithMinor + numFields = numParamsMotivesIthMinorFields)
    {j k : Nat}
    (hj : j ≤ numParamsMotivesIthMinorFields)
    (ihTele : Ctx numParamsMotivesIthMinorFields k)
    (recFields : List (RecFieldSeed (numParamsMotives + numMinors) numFields)) :
    Tele ParamRec (numParamsMotives + ithMinor) j →
    MetaM (Σ nRec : Nat, Ctx numParamsMotivesIthMinorFields nRec × List (RecFieldSeed (numParamsMotives + numMinors) numFields))
  | .nil => return ⟨k, ihTele, recFields⟩
  | .snoc (b := idx) fs f => do
      have hIdx : idx < numParamsMotivesIthMinorFields := by omega
      let ⟨k, ihTele, recFields⟩ ←
        buildIhs numParamsMotives numMinors ithMinor motiveVal numParamsMotivesIthMinorFields numFields him hle (hj := Nat.le_of_lt hIdx) ihTele recFields fs
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

      let indices₁ ← indices₁.mapM (fun t => (t.eval Env.infer))

      let fieldVar : VTm nestedEnd₁ := VTm.varAt idx
      let nestedArgs : List (VTm nestedEnd₁) :=
        List.finRange numNested |>.map fun j => VTm.varAt (numParamsMotivesIthMinorFields + j.val)
      let recVal ← fieldVar.apps nestedArgs

      let ih : VTm nestedEnd₁ := motiveVal.weaken
      let ih ← ih.apps indices₁
      let ih ← ih.app recVal
      let ih ← ih.quote
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
      let nestedTele₂ : Ctx rhsCtx nestedEnd₂ :=
        hEnd₂ ▸ hStart₂ ▸ (info.nestedTele.shiftAt idx minorsAfter).shift fieldsAfter

      let indices₂ : List (Tm nestedEnd₂) :=
        info.indices.map fun t =>
          let t := t.shiftAfter info.nestedEnd minorsAfter
          let t := t.shiftAfter (info.nestedEnd + minorsAfter) fieldsAfter
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
    OptionT MetaM (Param (numParams + 1 + ithMinor) × RuleSeed (numParams + 1 + numMinors)) := do
  let numParamsMotivesIthMinor : Nat := numParams + 1 + ithMinor
  let numParamsMotivesMinors := numParams + 1 + numMinors
  let ctorFieldsTy ← ctorFieldsTy.eval Env.infer
  let ctorFieldsTy : VTy numParamsMotivesIthMinor := ctorFieldsTy.weaken
  let ctorFieldsTy : Ty numParamsMotivesIthMinor ← ctorFieldsTy.quote
  let ⟨numParamsMotivesIthMinorFields, fieldTele, ctorRetTy⟩ := ctorFieldsTy.getTele
  let numFields := numParamsMotivesIthMinorFields - numParamsMotivesIthMinor

  let fieldTeleRec : Tele ParamRec numParamsMotivesIthMinor numParamsMotivesIthMinorFields ←
    fieldTele.mapM fun {jf} ⟨name, ty⟩ => do
      let recOpt ← analyseRecField numParams numIndices indName ctorName jf ty
      return ⟨name, ty, recOpt⟩

  have : numParamsMotivesIthMinor ≤ numParamsMotivesIthMinorFields := fieldTele.le

  let ⟨ihEnd, ihTele, recFields⟩ ←
    buildIhs (numParams + 1) numMinors ithMinor motiveVal numParamsMotivesIthMinorFields numFields him (by omega) (hj := Nat.le_refl _) .nil [] fieldTeleRec

  let resultCtx : Nat := ihEnd

  have := ihTele.le
  let fieldsVars : List (VTm resultCtx) :=
    List.finRange numFields |>.map fun i => VTm.varAt (numParamsMotivesIthMinor + i.val)

  let ctorApp : VTm resultCtx := VTm.const ctorName indUnivs
  let ctorApp ← ctorApp.apps (weaken params)
  let ctorApp ← ctorApp.apps fieldsVars

  let ctorIdxVals ←
    match ctorRetTy with
    | .el tm =>
        let (head, args) := tm.getAppArgs
        let .const name _ := head
          | raiseError (Error.ctorMustReturnInductive ctorName indName)
        if name != indName then
          raiseError (Error.ctorMustReturnInductive ctorName indName)
        indConsistency numParams numIndices indName ctorName args
    | .u _ => raiseError (Error.ctorMustReturnInductive ctorName indName)
    | .pi .. => raiseError (.msg "Internal error")
  let ctorIdxVals ← ctorIdxVals.mapM (fun t => (t.eval Env.infer))
  let ctorIdxVals := ctorIdxVals.map VTm.weaken

  let minorTy : VTm resultCtx := motiveVal.weaken
  let minorTy ← minorTy.apps ctorIdxVals
  let minorTy ← minorTy.app ctorApp
  let minorTy ← minorTy.quote
  let minorTy := Ty.el minorTy
  let minorTy := Ty.pis ihTele minorTy
  let minorTy := Ty.pis fieldTele minorTy

  return (⟨ctorName, minorTy⟩, ⟨ctorName, numFields, recFields⟩)

@[specialize]
def buildRecRule
    (numParams numMinors : Nat)
    (motiveVal : VTm (numParams + 1))
    (motiveUnivName : Name)
    (indUnivs : List Universe)
    (recName : Name)
    (params : List (VTm numParams))
    (i : Fin numMinors)
    (seed : RuleSeed (numParams + 1 + numMinors)) :
    OptionT MetaM (RecursorRule (numParams + 1 + numMinors)) := do
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

    let indices ← rf.indices.mapM (fun t => (t.eval Env.infer))

    let nestedArgs : List (VTm numParamsMotivesMinorsFieldsNested) :=
      List.finRange numNested |>.map fun j => VTm.varAt (numParamsMotivesMinorsFields + j.val)

    let majorArg : VTm numParamsMotivesMinorsFieldsNested := VTm.varAt (numParamsMotivesMinors + rf.fieldIdx.val)
    let majorArg ← majorArg.apps nestedArgs

    let recUnivs := .level motiveUnivName :: indUnivs
    let recVal : VTm numParamsMotivesMinorsFieldsNested := VTm.const recName recUnivs
    let recVal ← recVal.apps (weaken params (by omega))
    let recVal ← recVal.app (motiveVal.weaken (by omega))
    let recVal ← recVal.apps minors
    let recVal ← recVal.apps indices
    let recVal ← recVal.app majorArg
    let recVal ← recVal.quote
    let recVal := Tm.lams rf.nestedTele recVal
    (recVal.eval Env.infer)

  let fieldsVals : List (VTm numParamsMotivesMinorsFields) :=
    List.finRange numFields |>.map fun j => VTm.varAt (numParamsMotivesMinors + j.val)

  let rhsVal : VTm numParamsMotivesMinorsFields := VTm.varAt (numParamsMotives + i.val)
  let rhsVal ← rhsVal.apps fieldsVals
  let rhsVal ← rhsVal.apps ihVals
  let rhsVal ← rhsVal.quote

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
    OptionT MetaM (Ctx (numParams + 1) (numParams + 1 + numMinors) × Vector (RuleSeed (numParams + 1 + numMinors)) numMinors) := do
  if h' : ithMinor < numMinors then
    let (ctorName, ctorFieldsTy) := ctors[ithMinor]
    let (p, seed) ← buildMinorTy numParams numIndices numMinors indName indUnivs motiveVal params ctorName ithMinor (Nat.le_of_lt h') ctorFieldsTy
    let acc := acc.snoc p
    goMinors numParams numIndices numMinors indName indUnivs motiveVal params ctors (ithMinor + 1) (by omega) acc (seeds.push seed)
  else
    have hEq : ithMinor = numMinors := by omega
    have hk : numParams + 1 + ithMinor = numParams + 1 + numMinors := by omega
    return (hk ▸ acc, hEq ▸ seeds)

def elabInductive (ind : Inductive) : OptionT MetaM InductiveResult := do
  let numParams := ind.params.length
  let numMotives := 1
  let numParamsMotives := numParams + numMotives
  let (paramCtx, paramTys) ← withChild 2 (elabParams ind.params)
  let params := List.finRange numParams |>.map VTm.var
  let resultTy : Ty numParams ←
    match ind.tyOpt with
    | none => pure (Ty.u .zero)
    | some ty => withChild 3 (checkTy paramCtx ty)
  withChild 0 (emitHover (.signature ind.name paramTys resultTy))
  let indTy : Ty 0 := Ty.pis paramTys resultTy
  let univParams ← getUnivParams

  let _ ← addConstant ind.name (.opaque { univParams, ty := indTy })

  let ⟨numParamsIndices, indexTys, returnTy⟩ := resultTy.getTele
  let numIndices := numParamsIndices - numParams
  let resultUniv ← match returnTy with
    | .u u => pure u
    | .el _ => raiseError (.inductiveReturnTypeMustBeTypeUniverse ind.name)
    | .pi _ _ => raiseError (.msg "internal error")

  let indUnivs := univParams.map Universe.level
  let indVal : VTm 0 := VTm.const ind.name indUnivs

  let motiveIndices : List (VTm numParamsIndices) :=
    List.finRange numIndices |>.map fun i => VTm.varAt (numParams + i.val)

  let motiveInd : VTm numParamsIndices := indVal.weaken
  let motiveInd ← motiveInd.apps (weaken params indexTys.le)
  let motiveInd ← motiveInd.apps motiveIndices
  let motiveInd ← motiveInd.quote

  let motiveUnivName := Universe.freshName univParams
  let motiveTy : Ty numParams :=
    Ty.pis indexTys <|
    Ty.arrow (Ty.el motiveInd) <|
    Ty.u (.level motiveUnivName)
  let motiveVal : VTm numParamsMotives := VTm.varAt numParams

  let numMinors := ind.ctors.length
  let indTyVal : VTy 0 ← indTy.eval .nil
  let indTyVal : VTy numParams := indTyVal.weaken
  let ctors ← (Vector.finRange numMinors).mapM fun i =>
    withChild (4 + i.val) (
      elabCtor numParams numIndices ind.name indUnivs indTyVal resultUniv paramCtx
        (ind.ctors.get ⟨i.val, i.isLt⟩))

  let ctorEntries : List (Name × Constant) := ctors.toList.map fun (name, ctorFieldsTy) =>
    let ctorFieldsTy := Ty.pis paramTys ctorFieldsTy
    (name, .constructor { univParams, ty := ctorFieldsTy, indName := ind.name })

  for (name, entry) in ctorEntries do
    let _ ← addConstant name entry

  let numParamsMotivesMinors := numParamsMotives + numMinors

  let ctorNames := ctors.map Prod.fst

  let indEntry : Name × Constant := (ind.name, .inductive { univParams, ty := indTy, numParams, numIndices, numMinors, ctorNames })

  let recName := ind.name.str "rec"

  let (minorTys, seeds) ←
    goMinors numParams numIndices numMinors ind.name indUnivs motiveVal params ctors 0 (Nat.zero_le numMinors) .nil ⟨#[], rfl⟩

  let numParamsMotivesMinorsIndices := numParamsMotivesMinors + numIndices
  let indexTys' : Ctx numParamsMotivesMinors numParamsMotivesMinorsIndices :=
    have h1 : numParams + (1 + numMinors) = numParamsMotivesMinors := by omega
    have h2 : numParamsIndices + (1 + numMinors) = numParamsMotivesMinorsIndices := by have := indexTys.le; omega
    h2 ▸ h1 ▸ shiftIndexTys (1 + numMinors) indexTys

  let recRules ← Vector.finRange numMinors
    |>.zip seeds
    |>.mapM fun (i, seed) =>
    buildRecRule numParams numMinors motiveVal motiveUnivName indUnivs recName params i seed

  let indicesVals : List (VTm numParamsMotivesMinorsIndices) :=
    List.finRange numIndices |>.map fun j => VTm.varAt (numParamsMotivesMinors + j.val)

  let majorTy : VTm numParamsMotivesMinorsIndices := indVal.weaken
  let majorTy ← majorTy.apps (weaken params)
  let majorTy ← majorTy.apps indicesVals
  let majorTy ← majorTy.quote
  let majorTy := Ty.el majorTy
  let majorVal : VTm (numParamsMotivesMinorsIndices + 1) := VTm.varAt numParamsMotivesMinorsIndices

  let conclusionTy : VTm (numParamsMotivesMinorsIndices + 1) := motiveVal.weaken
  let conclusionTy ← conclusionTy.apps (weaken indicesVals)
  let conclusionTy ← conclusionTy.app majorVal
  let conclusionTy ← conclusionTy.quote
  let conclusionTy := Ty.el conclusionTy

  let recTy : Ty 0 :=
    Ty.pis paramTys <|
    Ty.pi ⟨`motive, motiveTy⟩ <|
    Ty.pis minorTys <|
    Ty.pis indexTys' <|
    Ty.arrow majorTy <|
    conclusionTy

  let recUnivParams := motiveUnivName :: univParams
  let recEntry : Name × Constant := (recName, .recursor { univParams := recUnivParams, ty := recTy, recName, numParams, numMotives := 1, numMinors, numIndices, recRules })

  let _ ← addConstant recName recEntry.2
  replaceEntry ind.name indEntry.2

  return { indEntry, ctorEntries, recEntry }

end Qdt
