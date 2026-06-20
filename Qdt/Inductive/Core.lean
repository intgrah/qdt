module

public import Qdt.Inductive.Promote
public import Qdt.Inductive.Recursor

public section

namespace Qdt

open Lean (Name)
open Frontend (Ast Path)

variable (q₀ : Key)

public structure Inductive where
  name : Name
  recName : Name
  univParams : List Name
  params : List Ast
  tyOpt : Option Ast
  ctors : List InductiveConstructor

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

public structure InductiveResult (numParams : Nat) where
  indEntry : Name × Constant
  ctorEntries : List (Name × Constant)
  recEntry : Name × Constant
  ctorTys : List (Name × Ty numParams)

public def Inductive.elab' (ind : Inductive) :
    OptionT (ElabM q₀) (InductiveResult ind.params.length) := do
  let origNumParams := ind.params.length
  let (paramCtx, paramTys) ← withChild q₀ 2 (Params.elab q₀ ind.params)
  let resultTy : Ty origNumParams ←
    match ind.tyOpt with
    | none => pure (Ty.u .zero)
    | some ty => OptionT.lift (withChild q₀ 3 (checkTy q₀ paramCtx ty))
  let _ ← Universe.retryPostponed q₀
  let resultTy ← resultTy.zonk q₀
  let origParamTys : Ctx 0 origNumParams ← paramTys.mapM (fun (n, bi, t) => return (n, bi, ← t.zonk q₀))
  withChild q₀ 0 (emitHover q₀ (.signature ind.name origParamTys resultTy))
  let indTy : Ty 0 := Ty.pis origParamTys resultTy
  let univParams ← getUnivParams q₀

  addPending q₀ ind.name (.opaque { univParams, ty := indTy })

  let ⟨numParamsIndices, indexTys, returnTy⟩ := resultTy.getTele
  let origNumIndices := numParamsIndices - origNumParams
  let resultUniv ← match returnTy with
    | .u u => pure u
    | .el _ => raiseError q₀ (.inductiveReturnTypeMustBeTypeUniverse ind.name)
    | .pi _ _ _ _ => raiseError q₀ (.msg "internal error")

  let usedNames : Std.HashSet Name := univParams.foldl (·.insert ·) ∅
  let motiveUniv : Name := (mintFreshUnivNames usedNames 1).headD `u
  let indUnivs := univParams.map Universe.param
  let recIndUnivs := indUnivs
  let indVal : VTm 0 := VTm.const ind.name indUnivs

  let numMinors := ind.ctors.length
  let indTyVal : VTy 0 ← indTy.eval q₀ .nil
  let indTyVal : VTy origNumParams := indTyVal.weaken
  let ctors ← (Vector.finRange numMinors).mapM fun i =>
    withChild q₀ (4 + i.val) <|
      (ind.ctors.get ⟨i.val, i.isLt⟩).elab q₀
        origNumIndices ind.name indUnivs indTyVal resultUniv paramCtx
  OptionT.lift (resumePostponed q₀ true)

  let ctorEntries ← ctors.toList.mapM fun (name, ctorFieldsTy) => do
    let ctorFullTy := Ty.pis origParamTys.toImplicit ctorFieldsTy
    let ctorFullTy ← ctorFullTy.zonk q₀
    return (name, Constant.constructor { univParams, ty := ctorFullTy, indName := ind.name })

  for (name, entry) in ctorEntries do
    addPending q₀ name entry

  let ctors ← ctors.mapM fun (n, ty) => do
    let ty ← ty.zonk q₀
    return (n, ty)
  let ⟨numPromoted, hPromotedLe⟩ := computeNumPromoted ind.name origNumIndices ctors.toList
  let plicities := match ctors.toList.head? with
    | some (_, ty) => ctorLeadingPlicities numPromoted ty
    | none => []

  have hSplit_a : origNumParams ≤ origNumParams + numPromoted := Nat.le_add_right ..
  have hSplit_b : origNumParams + numPromoted ≤ numParamsIndices := by
    have : numParamsIndices = origNumParams + origNumIndices := by
      have := indexTys.le
      omega
    omega
  let (promotedTysRaw, remainingIndexTys) :=
    indexTys.splitAt (origNumParams + numPromoted) hSplit_a hSplit_b

  let promotedTys : Ctx origNumParams (origNumParams + numPromoted) :=
    promotedTysRaw.map fun {n : Nat} (name, _, ty) =>
      let i := n - origNumParams
      let bi := plicities[i]?.getD .explicit
      ((name, bi, ty) : Name × BinderInfo × Ty n)

  let numParams := origNumParams + numPromoted
  let numIndices := origNumIndices - numPromoted
  let numParamsIndices_proof : numParams + numIndices = origNumParams + origNumIndices := by omega
  let paramTys : Ctx 0 numParams := origParamTys.append promotedTys
  let indexTys : Ctx numParams (numParams + numIndices) := numParamsIndices_proof ▸ (by
    have : numParamsIndices = origNumParams + origNumIndices := by
      have := indexTys.le
      omega
    exact this ▸ remainingIndexTys)
  let params := List.finRange numParams |>.map VTm.var

  let origCtors := ctors

  let ctors : Vector (Name × Ty numParams) numMinors ← ctors.mapM fun (name, ctorTy) => do
    let ⟨fieldEnd, fieldTele, retTy⟩ := ctorTy.getTele
    have h_a : origNumParams ≤ numParams := Nat.le_add_right ..
    if h_b : numParams ≤ fieldEnd then
      let (_, remainingFields) := fieldTele.splitAt numParams h_a h_b
      let newCtorTy : Ty numParams := Ty.pis remainingFields retTy
      return (name, newCtorTy)
    else
      raiseError q₀ (.msg s!"internal: constructor {name} has fewer fields than the auto-promoted count")

  let numParamsMotives := numParams + 1
  let motiveIndices : List (VTm (numParams + numIndices)) :=
    List.finRange numIndices |>.map fun i => VTm.varAt (numParams + i.val)

  let indValRec : VTm 0 := VTm.const ind.name recIndUnivs
  let motiveInd : VTm (numParams + numIndices) := indValRec.weaken
  let motiveInd ← motiveInd.apps q₀ (weaken params)
  let motiveInd ← motiveInd.apps q₀ motiveIndices
  let motiveInd ← motiveInd.quote q₀

  let motiveTy : Ty numParams :=
    Ty.pis indexTys <|
    Ty.arrow (Ty.el motiveInd) <|
    Ty.u (.param motiveUniv)
  let motiveVal : VTm numParamsMotives := VTm.varAt numParams

  let numParamsMotivesMinors := numParamsMotives + numMinors

  let ctorNames := ctors.map Prod.fst

  let indTyZ ← indTy.zonk q₀
  let indInfo : InductiveInfo := {
    univParams
    ty := indTyZ
    numParams
    numIndices
    numCtors := numMinors
    ctorNames
  }
  let indEntry : Name × Constant := (ind.name, .inductive indInfo)

  let recName := ind.recName

  let ctors ← ctors.mapM fun (n, ty) => do
    let ty ← ty.zonk q₀
    return (n, ty)
  let ctorsRec := ctors
  let (minorTys, seeds) ←
    goMinors q₀ numParams numIndices numMinors ind.name recIndUnivs motiveVal params ctorsRec 0 (Nat.zero_le numMinors) .nil ⟨#[], rfl⟩

  let numParamsMotivesMinorsIndices := numParamsMotivesMinors + numIndices
  let indexTys' : Ctx numParamsMotivesMinors numParamsMotivesMinorsIndices :=
    have h1 : numParams + (1 + numMinors) = numParamsMotivesMinors := by omega
    have h2 : (numParams + numIndices) + (1 + numMinors) = numParamsMotivesMinorsIndices := by omega
    h2 ▸ h1 ▸ shiftIndexTys (1 + numMinors) indexTys

  let recRules ← Vector.finRange numMinors
    |>.zip seeds
    |>.mapM fun (i, seed) =>
    buildRecRule q₀ motiveVal (.param motiveUniv) recIndUnivs recName params i seed

  let indicesVals : List (VTm numParamsMotivesMinorsIndices) :=
    List.finRange numIndices |>.map fun j => VTm.varAt (numParamsMotivesMinors + j.val)

  let majorTy : VTm numParamsMotivesMinorsIndices := indVal.weaken
  let majorTy ← majorTy.apps q₀ (weaken params)
  let majorTy ← majorTy.apps q₀ indicesVals
  let majorTy ← majorTy.quote q₀
  let majorTy := Ty.el majorTy
  let majorVal : VTm (numParamsMotivesMinorsIndices + 1) := VTm.varAt numParamsMotivesMinorsIndices

  let conclusionTy : VTm (numParamsMotivesMinorsIndices + 1) := motiveVal.weaken
  let conclusionTy ← conclusionTy.apps q₀ (weaken indicesVals)
  let conclusionTy ← conclusionTy.app q₀ majorVal
  let conclusionTy ← conclusionTy.quote q₀
  let conclusionTy := Ty.el conclusionTy

  let recTy : Ty 0 :=
    Ty.pis paramTys.toImplicit <|
    Ty.pi `motive .implicit motiveTy <|
    Ty.pis minorTys <|
    Ty.pis indexTys'.toImplicit <|
    Ty.arrow majorTy <|
    conclusionTy

  let recTy ← recTy.zonk q₀
  let recInfo : RecursorInfo := {
    univParams := motiveUniv :: univParams
    ty := recTy
    recName
    numParams
    numMotives := 1
    numMinors
    numIndices
    numPointCtors := numMinors
    recRules
  }
  let recEntry : Name × Constant := (recName, .recursor recInfo)

  addPending q₀ recName recEntry.2
  addPending q₀ ind.name indEntry.2

  let ctorTysReturn ← origCtors.toList.mapM fun (n, ty) => do
    let ty ← ty.zonk q₀
    return (n, ty)
  return { indEntry, ctorEntries, recEntry, ctorTys := ctorTysReturn }

end Qdt
