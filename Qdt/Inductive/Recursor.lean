module

public import Qdt.Inductive.Constructor

public section

namespace Qdt

open Lean (Name)

variable (q₀ : Key)

public structure ParamRec (n : Nat) where
  name : Name
  ty : Ty n
  recOpt : Option (RecFieldInfo n)

public structure RecFieldSeed (numParamsMotivesMinors numFields : Nat) where
  fieldIdx : Fin numFields
  nestedEnd : Nat
  nestedTele : Ctx (numParamsMotivesMinors + numFields) nestedEnd
  indices : List (Tm nestedEnd)

public structure RuleSeed (numParamsMotivesMinors : Nat) where
  ctorName : Name
  numFields : Nat
  recFields : List (RecFieldSeed numParamsMotivesMinors numFields)

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
    ElabM q₀ (Σ nRec : Nat, Ctx numParamsMotivesIthMinorFields nRec × List (RecFieldSeed (numParamsMotives + numMinors) numFields))
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
        hEnd ▸ hStart ▸ info.nestedTele.dmap fieldsAfter fun {n : Nat} ⟨name, bi, ty⟩ =>
          ⟨name, bi, ty.shiftAfter (n - idx) fieldsAfter⟩
      let indices₁ : List (Tm nestedEnd₁) :=
        info.indices.map (hEnd ▸ ·.shiftAfter numNested fieldsAfter)

      let indices₁ ← indices₁.mapM (fun t => (t.eval q₀ Env.infer))

      let fieldVar : VTm nestedEnd₁ := VTm.varAt idx
      let nestedArgs : List (VTm nestedEnd₁) :=
        List.finRange numNested |>.map fun j => VTm.varAt (numParamsMotivesIthMinorFields + j.val)
      let recVal ← fieldVar.apps q₀ nestedArgs

      let ih : VTm nestedEnd₁ := motiveVal.weaken
      let ih ← ih.apps q₀ indices₁
      let ih ← ih.app q₀ recVal
      let ih ← ih.quote q₀
      let ih := Ty.el ih
      let ih := Ty.pis nestedTele₁ ih

      let ihName := f.name.str "ih"
      let numIhsSoFar := k - numParamsMotivesIthMinorFields
      have hShift : numParamsMotivesIthMinorFields + numIhsSoFar = k := by
        have : numParamsMotivesIthMinorFields ≤ k := ihTele.le
        omega
      let ihTy : Ty k := hShift ▸ ih.shift numIhsSoFar
      let ihTele := ihTele.snoc ⟨ihName, .explicit, ihTy⟩

      let minorsAfter : Nat := numMinors - ithMinor
      let rhsCtx := numParamsMotivesMinors + numFields
      let nestedEnd₂ : Nat := rhsCtx + numNested
      have hStart₂ : idx + minorsAfter + fieldsAfter = rhsCtx := by omega
      have hEnd₂ : info.nestedEnd + minorsAfter + fieldsAfter = nestedEnd₂ := by omega
      let numParamsMotivesIthMinor := numParamsMotives + ithMinor
      have hAssoc1 : idx + (minorsAfter + fieldsAfter) = idx + minorsAfter + fieldsAfter := by omega
      have hAssoc2 : info.nestedEnd + (minorsAfter + fieldsAfter) = info.nestedEnd + minorsAfter + fieldsAfter := Nat.add_assoc _ _ _ |>.symm
      let nestedTele₂ : Ctx rhsCtx nestedEnd₂ :=
        hEnd₂ ▸ hStart₂ ▸ hAssoc1 ▸ hAssoc2 ▸ info.nestedTele.dmap (minorsAfter + fieldsAfter) fun {n : Nat} ⟨name, bi, ty⟩ =>
          let ty := ty.shiftAfter (n - idx) fieldsAfter
          have : n + fieldsAfter + minorsAfter = n + (minorsAfter + fieldsAfter) := by omega
          ⟨name, bi, this ▸ ty.shiftAfter (n - numParamsMotivesIthMinor + fieldsAfter) minorsAfter⟩

      let indices₂ : List (Tm nestedEnd₂) :=
        info.indices.map fun t =>
          let numNested := info.nestedEnd - idx
          let t := t.shiftAfter numNested fieldsAfter
          have : info.nestedEnd + fieldsAfter + minorsAfter = info.nestedEnd + minorsAfter + fieldsAfter := by omega
          let t : Tm (info.nestedEnd + minorsAfter + fieldsAfter) := this ▸ t.shiftAfter (info.nestedEnd - numParamsMotivesIthMinor + fieldsAfter) minorsAfter
          hEnd₂ ▸ t

      have hFieldIdx : idx - numParamsMotivesIthMinor < numFields := by
        have := fs.le
        omega
      let fieldIdx : Fin numFields := ⟨idx - numParamsMotivesIthMinor, hFieldIdx⟩
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
    OptionT (ElabM q₀) ((Name × BinderInfo × Ty (numParams + 1 + ithMinor)) × RuleSeed (numParams + 1 + numMinors)) := do
  let numParamsMotivesIthMinor : Nat := numParams + 1 + ithMinor
  let numParamsMotivesMinors := numParams + 1 + numMinors
  let ctorFieldsTy ← ctorFieldsTy.eval q₀ Env.infer
  let ctorFieldsTy : VTy numParamsMotivesIthMinor := ctorFieldsTy.weaken
  let ctorFieldsTy : Ty numParamsMotivesIthMinor ← ctorFieldsTy.quote q₀
  let ⟨numParamsMotivesIthMinorFields, fieldTele, ctorRetTy⟩ := ctorFieldsTy.getTele
  let numFields := numParamsMotivesIthMinorFields - numParamsMotivesIthMinor

  let fieldTeleRec : Tele ParamRec numParamsMotivesIthMinor numParamsMotivesIthMinorFields ←
    fieldTele.mapM fun {jf} ⟨name, _, ty⟩ => do
      let recOpt ← analyseRecField q₀ numParams numIndices indName ctorName jf ty
      return ⟨name, ty, recOpt⟩

  have : numParamsMotivesIthMinor ≤ numParamsMotivesIthMinorFields := fieldTele.le

  let ⟨ihEnd, ihTele, recFields⟩ ←
    buildIhs q₀ numParamsMotivesIthMinorFields numFields
      motiveVal him (by omega) (hj := Nat.le_refl _) .nil [] fieldTeleRec

  let resultCtx : Nat := ihEnd

  have := ihTele.le
  let fieldsVars : List (VTm resultCtx) :=
    List.finRange numFields |>.map fun i => VTm.varAt (numParamsMotivesIthMinor + i.val)

  let ctorApp : VTm resultCtx := VTm.const ctorName indUnivs
  let ctorApp ← ctorApp.apps q₀ (weaken params)
  let ctorApp ← ctorApp.apps q₀ fieldsVars

  let ctorIdxVals ←
    match ctorRetTy with
    | .el tm =>
        let (head, args) := tm.getAppArgs
        let .const name _ := head
          | raiseError q₀ (Error.ctorMustReturnInductive ctorName indName)
        if name != indName then
          raiseError q₀ (Error.ctorMustReturnInductive ctorName indName)
        indConsistency q₀ numParams numIndices indName ctorName args
    | .u _ => raiseError q₀ (Error.ctorMustReturnInductive ctorName indName)
    | .pi .. => raiseError q₀ (.msg "Internal error")
  let ctorIdxVals ← ctorIdxVals.mapM (fun t => (t.eval q₀ Env.infer))
  let ctorIdxVals := ctorIdxVals.map VTm.weaken

  let minorTy : VTm resultCtx := motiveVal.weaken
  let minorTy ← minorTy.apps q₀ ctorIdxVals
  let minorTy ← minorTy.app q₀ ctorApp
  let minorTy ← minorTy.quote q₀
  let minorTy := Ty.el minorTy
  let minorTy := Ty.pis ihTele minorTy
  let minorTy := Ty.pis fieldTele minorTy

  return (⟨ctorName, .explicit, minorTy⟩, ⟨ctorName, numFields, recFields⟩)

@[specialize]
def buildRecRule {numParams numMinors}
    (motiveVal : VTm (numParams + 1))
    (motiveUniv : Universe)
    (recIndUnivs : List Universe)
    (recName : Name)
    (params : List (VTm numParams))
    (i : Fin numMinors)
    (seed : RuleSeed (numParams + 1 + numMinors)) :
    OptionT (ElabM q₀) (RecursorRule (numParams + 1 + numMinors)) := do
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

    let indices ← rf.indices.mapM (fun t => (t.eval q₀ Env.infer))

    let nestedArgs : List (VTm numParamsMotivesMinorsFieldsNested) :=
      List.finRange numNested |>.map fun j => VTm.varAt (numParamsMotivesMinorsFields + j.val)

    let majorArg : VTm numParamsMotivesMinorsFieldsNested := VTm.varAt (numParamsMotivesMinors + rf.fieldIdx.val)
    let majorArg ← majorArg.apps q₀ nestedArgs

    let recUnivs := motiveUniv :: recIndUnivs
    let recVal : VTm numParamsMotivesMinorsFieldsNested := VTm.const recName recUnivs
    let recVal ← recVal.apps q₀ (weaken params (by omega))
    let recVal ← recVal.app q₀ (motiveVal.weaken (by omega))
    let recVal ← recVal.apps q₀ minors
    let recVal ← recVal.apps q₀ indices
    let recVal ← recVal.app q₀ majorArg
    let recVal ← recVal.quote q₀
    let recVal := Tm.lams rf.nestedTele recVal
    (recVal.eval q₀ Env.infer)

  let fieldsVals : List (VTm numParamsMotivesMinorsFields) :=
    List.finRange numFields |>.map fun j => VTm.varAt (numParamsMotivesMinors + j.val)

  let rhsVal : VTm numParamsMotivesMinorsFields := VTm.varAt (numParamsMotives + i.val)
  let rhsVal ← rhsVal.apps q₀ fieldsVals
  let rhsVal ← rhsVal.apps q₀ ihVals
  let rhsVal ← rhsVal.quote q₀

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
    OptionT (ElabM q₀) (Ctx (numParams + 1) (numParams + 1 + numMinors) × Vector (RuleSeed (numParams + 1 + numMinors)) numMinors) := do
  if h' : ithMinor < numMinors then
    let (ctorName, ctorFieldsTy) := ctors[ithMinor]
    let (p, seed) ←
      buildMinorTy q₀ numParams numIndices numMinors
        indName indUnivs motiveVal params ctorName ithMinor (Nat.le_of_lt h') ctorFieldsTy
    let acc := acc.snoc p
    goMinors numParams numIndices numMinors
      indName indUnivs motiveVal params ctors
      (ithMinor + 1) (by omega) acc (seeds.push seed)
  else
    have hEq : ithMinor = numMinors := by omega
    have hk : numParams + 1 + ithMinor = numParams + 1 + numMinors := by omega
    return (hk ▸ acc, hEq ▸ seeds)

end Qdt
