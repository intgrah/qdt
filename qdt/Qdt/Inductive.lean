import Qdt.MLTT.Shift
import Qdt.Control
import Qdt.Frontend.Ast
import Qdt.Params
import Qdt.Nbe
import Qdt.Quote

namespace Qdt

export Lean (Name)

/-- Destructure an App chain into its head and spine -/
private def Tm.getAppArgs {n} : Tm n → Tm n × List (Tm n) :=
  let rec go {n} (spine : List (Tm n)) : Tm n → Tm n × List (Tm n)
    | .app f a => go (a :: spine) f
    | t => (t, spine)
  go []

def Ty.getTele {a} : Ty a → Σ b, Tele Param a b × Ty b :=
  let rec go {a b}
      (acc : Tele Param a b) :
      Ty b →
      Σ nb : Nat, Tele Param a nb × Ty nb
    | .pi param b => go (acc.snoc param) b
    | t => ⟨b, acc, t⟩
  go Tele.nil

private unsafe def weaken_impl {n m} : List (VTm n) → (_ : n ≤ m) → List (VTm m) := unsafeCast

-- @[implemented_by weaken_impl]
private def weaken' {n m} (ts : List (VTm n)) (h : n ≤ m) : List (VTm m) :=
  ts.map (VTm.weaken h)

def weaken {n m} (ts : List (VTm n)) (h : n ≤ m := by omega) : List (VTm m) := weaken' ts h

private def Env.infer : {n : Nat} → Env n n
  | 0 => Env.nil
  | n + 1 => Env.infer.weaken.cons (VTm.varAt n)

mutual

private def Tm.hasIndOcc {n} (ind : Name) : Tm n → Bool
  | .var _ => false
  | .const name => name == ind
  | .lam ⟨_, a⟩ b => a.hasIndOcc ind || b.hasIndOcc ind
  | .app a b => a.hasIndOcc ind || b.hasIndOcc ind
  | .piHat _ a b => a.hasIndOcc ind || b.hasIndOcc ind
  | .proj _ a => a.hasIndOcc ind
  | .letE _ a b c => a.hasIndOcc ind || b.hasIndOcc ind || c.hasIndOcc ind

private def Ty.hasIndOcc {n} (ind : Name) : Ty n → Bool
  | .u => false
  | .pi ⟨_, a⟩ b => a.hasIndOcc ind || b.hasIndOcc ind
  | .el a => a.hasIndOcc ind

end

private structure RecFieldInfo (n : Nat) where
  nestedEnd : Nat
  nestedTele : Tele Param n nestedEnd
  indices : List (Tm nestedEnd)

private structure ParamRec (n : Nat) where
  name : Name
  ty : Ty n
  recOpt : Option (RecFieldInfo n)

private structure RecFieldSeed (numParamsMotivesMinors numFields : Nat) where
  fieldIdx : Fin numFields
  nestedEnd : Nat
  nestedTele : Tele Param (numParamsMotivesMinors + numFields) nestedEnd
  indices : List (Tm nestedEnd)

private structure RuleSeed (numParamsMotivesMinors : Nat) where
  ctorName : Name
  numFields : Nat
  recFields : List (RecFieldSeed numParamsMotivesMinors numFields)

def Tele.shiftAt {a b} (cutoff s : Nat) (tele : Tele Param a b) : Tele Param (a + s) (b + s) :=
  tele.dmap s fun {n} ⟨name, ty⟩ => ⟨name, ty.shiftAfter (n + cutoff) s⟩

def Tele.shift {m k} := @Tele.shiftAt m k 0

/--
Given a recursive occurrence of the inductive type, check that:
- It is applied to the correct number of parameters and indices.
- The parameters exactly match the parameters in the type former, in order.
- The indices do not contain the inductive type.
Returns the indices.
-/
private def indConsistency {n}
    (numParams numIndices : Nat)
    (indName : Name)
    (args : List (Tm n)) :
    CoreM (List (Tm n)) := do
  if args.length != numParams + numIndices then
    throw (.msg "Invalid occurrence of inductive type")
  let (params, indices) := args.splitAt numParams
  for (ithParam, param) in params.mapIdx Prod.mk do
    let .var j := param
      | throw (.msg "Inconsistent parameters: must be a bound variable")
    if ithParam + j.val + 1 != n then
      throw (.msg "Inconsistent parameters: must match parameters in order")
  for index in indices do
    if index.hasIndOcc indName then
      throw (.msg "Inductive type occurs in an invalid position")
  return indices

private def analyseRecField
    (numParams numIndices : Nat)
    (indName : Name)
    (jthFieldCtx : Nat)
    (fty : Ty jthFieldCtx) :
    CoreM (Option (RecFieldInfo jthFieldCtx)) := do
  let ⟨nb, nestedTele, endTy⟩ := fty.getTele
  if nestedTele.any (fun ⟨_, t⟩ => t.hasIndOcc indName) then
    throw (.msg "Inductive type occurs in a negative position")
  match endTy with
  | .u => throw (.msg "Constructor fields must be small types")
  | .el tm => do
      let (head, args) := tm.getAppArgs
      if let .const name := head then
        if name == indName then
          let indices ← indConsistency numParams numIndices indName args
          return some { nestedEnd := nb, nestedTele, indices : RecFieldInfo _ }
        else
          for arg in args do
            if arg.hasIndOcc indName then
              throw (.msg "Inductive type occurs in an invalid position")
          return none
      else
        if tm.hasIndOcc indName then
          throw (.msg "Inductive type occurs in an invalid position")
        return none
  | .pi .. => throw (.msg "Internal error")

def elabCtor
    (numParams numIndices : Nat)
    (indName : Name)
    (paramCtx : TermContext numParams)
    (params : List (VTm numParams))
    (ctor : Frontend.Ast.Command.InductiveConstructor) :
    MetaM (Name × Ty numParams) := do
  if !ctor.name.isAtomic then
    throw (.msg s!"{ctor.name}: constructor name must be atomic")
  let ctorName := indName.append ctor.name
  let (fieldCtx, fieldTys) ← elabParamsFrom ctor.fields paramCtx
  let retTy ←
    match ctor.tyOpt with
    | some retTy =>
      checkTy retTy fieldCtx
    | none => do
        if numIndices > 0 then
          throw (.indexedTypeCtorReturnTypeRequired ctor.src ctorName)
        let res : VTm (numParams + ctor.fields.length) := VTm.const indName
        let res ← res.apps (weaken params)
        let res ← res.quote
        pure (Ty.el res)
  return (ctorName, Ty.pis fieldTys retTy)

def elabInductive (ind : Frontend.Ast.Command.Inductive) : MetaM Unit := do
  let numParams := ind.params.length
  let numMotives := 1
  let numParamsMotives := numParams + numMotives
  let (paramCtx, paramTys) ← elabParams ind.params
  let params := List.finRange numParams |>.map VTm.var
  let resultTy : Ty numParams ←
    match ind.tyOpt with
    | none => pure Ty.u
    | some ty => checkTy ty paramCtx
  let indTy : Ty 0 := Ty.pis paramTys resultTy
  -- Insert the type former early so constructor types can reference the inductive.
  Global.addEntry ind.name (.opaque ⟨indTy⟩)

  let ⟨numParamsIndices, indexTys, returnTy⟩ := resultTy.getTele
  let numIndices := numParamsIndices - numParams
  if let .el _ := returnTy then
    throw (.msg "inductive return type must be Type")

  let indVal : VTm 0 := VTm.const ind.name

  let motiveIndices : List (VTm numParamsIndices) :=
    List.finRange numIndices |>.map fun i => VTm.varAt (numParams + i.val)

  let motiveInd : VTm numParamsIndices := indVal.weaken
  let motiveInd ← motiveInd.apps (weaken params indexTys.le)
  let motiveInd ← motiveInd.apps motiveIndices
  let motiveInd ← motiveInd.quote

  let motiveTy : Ty numParams :=
    Ty.pis indexTys <|
    Ty.arrow (Ty.el motiveInd) <|
    Ty.u
  let motiveVal : VTm numParamsMotives := VTm.varAt numParams

  let numMinors := ind.ctors.length
  let ctors : Vector _ numMinors := ⟨⟨ind.ctors⟩, rfl⟩
  let ctors ← ctors.mapM (elabCtor numParams numIndices ind.name paramCtx params)

  for (name, ctorFieldsTy) in ctors do
    let ctorFieldsTy := Ty.pis paramTys ctorFieldsTy
    Global.addEntry name (.constructor ⟨ctorFieldsTy, ind.name⟩)

  let numParamsMotivesMinors := numParamsMotives + numMinors

  let ctorNames := ctors.map Prod.fst

  Global.replaceEntry ind.name (.inductive {
    ty := indTy,
    numParams,
    numIndices,
    numMinors,
    ctorNames,
  })

  -- Recursor generation (minors + iota rules)

  let recName := ind.name.str "rec"

  let buildMinorTy
      (ctorName : Name)
      (ithMinor : Nat)
      (him : ithMinor ≤ numMinors)
      (ctorFieldsTy : Ty numParams) :
      MetaM (Param (numParamsMotives + ithMinor) × RuleSeed numParamsMotivesMinors) := do
    let numParamsMotivesIthMinor : Nat := numParamsMotives + ithMinor
    let ctorFieldsTy ← ctorFieldsTy.eval Env.infer
    let ctorFieldsTy : VTy numParamsMotivesIthMinor := ctorFieldsTy.weaken
    let ctorFieldsTy : Ty numParamsMotivesIthMinor ← ctorFieldsTy.quote
    let ⟨numParamsMotivesIthMinorFields, fieldTele, ctorRetTy⟩ := ctorFieldsTy.getTele
    let numFields := numParamsMotivesIthMinorFields - numParamsMotivesIthMinor

    let fieldTeleRec : Tele ParamRec numParamsMotivesIthMinor numParamsMotivesIthMinorFields ←
      fieldTele.mapM fun {jf} ⟨name, ty⟩ => do
        let recOpt ← analyseRecField numParams numIndices ind.name jf ty
        return ⟨name, ty, recOpt⟩

    let rhsCtx := numParamsMotivesMinors + numFields
    have : numParamsMotivesIthMinor ≤ numParamsMotivesIthMinorFields := fieldTele.le

    let rec buildIhs
        {j k}
        (hj : j ≤ numParamsMotivesIthMinorFields)
        (ihTele : Tele Param numParamsMotivesIthMinorFields k)
        (recFields : List (RecFieldSeed numParamsMotivesMinors numFields)) :
        Tele ParamRec numParamsMotivesIthMinor j →
        MetaM (Σ nRec : Nat, Tele Param numParamsMotivesIthMinorFields nRec × List (RecFieldSeed numParamsMotivesMinors numFields))
      | .nil => return ⟨k, ihTele, recFields⟩
      | .snoc (b := idx) fs f => do
          have hIdx : idx < numParamsMotivesIthMinorFields := by omega
          let ⟨k, ihTele, recFields⟩ ←
            buildIhs (hj := Nat.le_of_lt hIdx) ihTele recFields fs
          let some info := f.recOpt
            | return ⟨k, ihTele, recFields⟩
          have : idx ≤ info.nestedEnd := info.nestedTele.le
          let numNested : Nat := info.nestedEnd - idx
          let fieldsAfter : Nat := numParamsMotivesIthMinorFields - idx

          have hStart : idx + fieldsAfter = numParamsMotivesIthMinorFields := by omega
          let nestedEnd₁ : Nat := numParamsMotivesIthMinorFields + numNested
          have hEnd : info.nestedEnd + fieldsAfter = nestedEnd₁ := by omega
          let nestedTele₁ : Tele Param numParamsMotivesIthMinorFields nestedEnd₁ :=
            hEnd ▸ hStart ▸ info.nestedTele.dmap fieldsAfter fun {n} ⟨name, ty⟩ =>
              ⟨name, ty.shiftAfter (n - idx) fieldsAfter⟩
          let indices₁ : List (Tm nestedEnd₁) :=
            info.indices.map fun t => hEnd ▸ t.shiftAfter numNested fieldsAfter

          let indices₁ ← indices₁.mapM fun t => t.eval Env.infer

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
          let nestedEnd₂ : Nat := rhsCtx + numNested
          have hStart₂ : idx + minorsAfter + fieldsAfter = rhsCtx := by omega
          have hEnd₂ : info.nestedEnd + minorsAfter + fieldsAfter = nestedEnd₂ := by omega
          let nestedTele₂ : Tele Param rhsCtx nestedEnd₂ :=
            hEnd₂ ▸ hStart₂ ▸ (info.nestedTele.shiftAt idx minorsAfter).shift fieldsAfter

          let indices₂ : List (Tm nestedEnd₂) :=
            info.indices.map fun t =>
              let t := t.shiftAfter info.nestedEnd minorsAfter
              let t := t.shiftAfter (info.nestedEnd + minorsAfter) fieldsAfter
              hEnd₂ ▸ t

          let fieldIdx : Fin numFields := ⟨idx - numParamsMotivesIthMinor, by have := fs.le; omega⟩
          let recFields := recFields ++ [{ fieldIdx, nestedEnd := nestedEnd₂, nestedTele := nestedTele₂, indices := indices₂ }]
          return ⟨k + 1, ihTele, recFields⟩

    let ⟨ihEnd, ihTele, recFields⟩ ←
      buildIhs (hj := Nat.le_refl numParamsMotivesIthMinorFields) .nil [] fieldTeleRec

    let resultCtx : Nat := ihEnd

    have := ihTele.le
    let fieldsVars : List (VTm resultCtx) :=
      List.finRange numFields |>.map fun i => VTm.varAt (numParamsMotivesIthMinor + i.val)

    let ctorApp : VTm resultCtx := VTm.const ctorName
    let ctorApp ← ctorApp.apps (weaken params)
    let ctorApp ← ctorApp.apps fieldsVars

    let ctorIdxVals ←
      match ctorRetTy with
      | .el tm =>
          let (head, args) := tm.getAppArgs
          let .const name := head
            | throw (.msg "Constructor return type must be the inductive type")
          if name != ind.name then
            throw (.msg "Constructor return type must be the inductive type")
          indConsistency numParams numIndices ind.name args
      | .u => throw (.msg "constructor return type must be the inductive type")
      | .pi .. => throw (.msg "Internal error")
    let ctorIdxVals ← ctorIdxVals.mapM (fun t => t.eval Env.infer)
    let ctorIdxVals := ctorIdxVals.map VTm.weaken

    let minorTy : VTm resultCtx := motiveVal.weaken
    let minorTy ← minorTy.apps ctorIdxVals
    let minorTy ← minorTy.app ctorApp
    let minorTy ← minorTy.quote
    let minorTy := Ty.el minorTy
    let minorTy := Ty.pis ihTele minorTy
    let minorTy := Ty.pis fieldTele minorTy

    return (⟨ctorName, minorTy⟩, ⟨ctorName, numFields, recFields⟩)
  let rec goMinors
      (ithMinor : Nat)
      (hi : ithMinor ≤ numMinors)
      (acc : Tele Param numParamsMotives (numParamsMotives + ithMinor))
      (seeds : Vector (RuleSeed numParamsMotivesMinors) ithMinor) :
      MetaM (Tele Param numParamsMotives numParamsMotivesMinors × Vector (RuleSeed numParamsMotivesMinors) numMinors) := do
    if h' : ithMinor < numMinors then
      let (ctorName, ctorFieldsTy) := ctors[ithMinor]'h'
      let (p, seed) ← buildMinorTy ctorName ithMinor (Nat.le_of_lt h') ctorFieldsTy
      let acc := acc.snoc p
      goMinors (ithMinor + 1) (by omega) acc (seeds.push seed)
    else
      have hEq : ithMinor = numMinors := by omega
      have hk : numParamsMotives + ithMinor = numParamsMotivesMinors := by omega
      return (hk ▸ acc, hEq ▸ seeds)

  let (minorTys, seeds) ←
    goMinors 0 (Nat.zero_le numMinors) .nil ⟨#[], rfl⟩

  let numParamsMotivesMinorsIndices := numParamsMotivesMinors + numIndices
  let indexTys' : Tele Param numParamsMotivesMinors numParamsMotivesMinorsIndices :=
    let rec goW {k} : Tele Param numParams k → Tele Param numParamsMotivesMinors (k + (1 + numMinors))
      | .nil =>
          have h : numParams + (1 + numMinors) = numParamsMotivesMinors := by omega
          h ▸ Tele.nil
      | .snoc (b := n) bs ⟨name, ty⟩ =>
          have h : n + (1 + numMinors) + 1 = n + 1 + (1 + numMinors) := by omega
          h ▸ (goW bs).snoc ⟨name, ty.shiftAfter (n - numParams) (1 + numMinors)⟩

    have : numParamsIndices + (numMotives + numMinors) = numParamsMotivesMinorsIndices := by have := indexTys.le; omega
    this ▸ goW indexTys

  -- Build recursor rules for iota reduction
  let recRules ← Vector.finRange numMinors
    |>.zip seeds
    |>.mapM fun (i, seed) => do
    let numFields := seed.numFields
    let numParamsMotivesMinorsFields : Nat := numParamsMotivesMinors + numFields

    let ihVals ← seed.recFields.mapM fun rf => do
      let numParamsMotivesMinorsFieldsNested : Nat := rf.nestedEnd
      let numNested : Nat := rf.nestedEnd - numParamsMotivesMinorsFields

      have : numParamsMotivesMinorsFields ≤ numParamsMotivesMinorsFieldsNested := rf.nestedTele.le
      let minors : List (VTm numParamsMotivesMinorsFieldsNested) :=
        List.finRange numMinors |>.map fun ithMinor => VTm.varAt (numParamsMotives + ithMinor.val)

      let indices ← rf.indices.mapM (fun t => t.eval Env.infer)

      let nestedArgs : List (VTm numParamsMotivesMinorsFieldsNested) :=
        List.finRange numNested |>.map fun j => VTm.varAt (numParamsMotivesMinorsFields + j.val)

      let majorArg : VTm numParamsMotivesMinorsFieldsNested := VTm.varAt (numParamsMotivesMinors + rf.fieldIdx.val)
      let majorArg ← majorArg.apps nestedArgs

      let recVal : VTm numParamsMotivesMinorsFieldsNested := VTm.const recName
      let recVal ← recVal.apps (weaken params (by omega))
      let recVal ← recVal.app (motiveVal.weaken (by omega))
      let recVal ← recVal.apps minors
      let recVal ← recVal.apps indices
      let recVal ← recVal.app majorArg
      let recVal ← recVal.quote
      let recVal := Tm.lams rf.nestedTele recVal
      recVal.eval Env.infer

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

  Global.addEntry recName (.recursor {
    ty := recTy,
    recName,
    numParams,
    numMotives := 1,
    numMinors,
    numIndices,
    recRules,
  })

end Qdt
