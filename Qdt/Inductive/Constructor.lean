module

public import Qdt.Inductive.Util
public import Qdt.Bidirectional
public import Qdt.Params
public import Qdt.Theory.Universe.LE

public section

namespace Qdt

open Lean (Name)
open Frontend (Ast Path)

variable (q₀ : Key)

public structure InductiveConstructor where
  name : Name
  fields : List Ast
  tyOpt : Option Ast
deriving Inhabited

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

public structure RecFieldInfo (n : Nat) where
  nestedEnd : Nat
  nestedTele : Ctx n nestedEnd
  indices : List (Tm nestedEnd)

def indConsistency {n : Nat}
    (numParams numIndices : Nat)
    (indName ctorName : Name)
    (args : List (Tm n)) :
    OptionT (ElabM q₀) (List (Tm n)) := do
  if args.length != numParams + numIndices then
    raiseError q₀ (.nonPositiveOccurrence indName)
  let (params, indices) := args.splitAt numParams
  for (ithParam, param) in params.mapIdx Prod.mk do
    let .var j := param
      | raiseError q₀ (.ctorParamMismatch ctorName)
    if ithParam + j.val + 1 != n then
      raiseError q₀ (.ctorParamMismatch ctorName)
  for index in indices do
    if index.hasIndOcc indName then
      raiseError q₀ (.nonPositiveOccurrence indName)
  return indices

def analyseRecField
    (numParams numIndices : Nat)
    (indName ctorName : Name)
    (jthFieldCtx : Nat)
    (fty : Ty jthFieldCtx) :
    OptionT (ElabM q₀) (Option (RecFieldInfo jthFieldCtx)) := do
  let ⟨nb, nestedTele, endTy⟩ := fty.getTele
  if nestedTele.any (fun ⟨_, _, t⟩ => t.hasIndOcc indName) then
    raiseError q₀ (.nonPositiveOccurrence indName)
  match endTy with
  | .u _ => return none
  | .el tm => do
      let (head, args) := tm.getAppArgs
      if let .const name _ := head then
        if name == indName then
          let indices ← indConsistency q₀ numParams numIndices indName ctorName args
          return some { nestedEnd := nb, nestedTele, indices : RecFieldInfo _ }
        else
          for arg in args do
            if arg.hasIndOcc indName then
              raiseError q₀ (.nonPositiveOccurrence indName)
          return none
      else
        if tm.hasIndOcc indName then
          raiseError q₀ (.nonPositiveOccurrence indName)
        return none
  | .pi .. => raiseError q₀ (.msg "Internal error")

def getTypedBinder' : Ast → Option (Name × BinderInfo × Ast)
  | .node `Binder.typed cs => some (cs[0]!.getName, .explicit, cs[1]!)
  | .node `Binder.implicit cs => some (cs[0]!.getName, .implicit, cs[1]!)
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
    OptionT (ElabM q₀) (Name × Ty numParams) := do
  if !ctor.name.isAtomic then
    raiseError q₀ (.ctorNameNotAtomic ctor.name)
  let ctorName := indName.append ctor.name
  let indParamCtx : TermContext (numParams + 1) ← paramCtx.bindV q₀ indName indTyVal
  let params : List (VTm (numParams + 1)) := List.finRange numParams |>.map fun i => VTm.varAt i.val
  let (fieldCtx, fieldTys, fieldUnivs) ← withChild q₀ 1 (Params.elabWithLevels q₀ indParamCtx ctor.fields)
  for ((field, fieldUniv), idx) in (ctor.fields.zip fieldUnivs).zipIdx do
    let fieldName := getFieldName' field |>.getD .anonymous
    Universe.propagateLE q₀ fieldUniv resultUniv
    let fieldUniv ← Universe.zonk q₀ fieldUniv
    if ¬ fieldUniv ≤ resultUniv then
      withChild q₀ 1 (withChild q₀ idx (withChild q₀ 1
        (raiseError q₀ (.fieldUniverseTooLarge ctorName fieldName fieldUniv resultUniv))))
  let numFields := ctor.fields.length
  let retTy ←
    match ctor.tyOpt with
    | some retTyAst =>
      OptionT.lift (withChild q₀ 2 (checkTy q₀ fieldCtx retTyAst))
    | none => do
        if numIndices > 0 then
          raiseError q₀ (Error.typeFamilyCtorReturnTypeRequired ctorName)
        let indVar : VTm (numParams + 1 + numFields) := VTm.varAt numParams
        let res ← indVar.apps q₀ (weaken params)
        let res ← res.quote q₀
        pure (Ty.el res)
  match retTy with
  | .el tm =>
      let (head, args) := tm.getAppArgs
      match head with
      | .var hj =>
          if hj.val == numFields then
            for i in List.finRange numParams do
              if let some arg := args[i.val]? then
                let provided ← OptionT.lift (arg.eval q₀ fieldCtx.env)
                let _ ← OptionT.lift (VTm.conv q₀ fieldCtx.ctx provided (VTm.varAt i.val (by omega)))
      | _ => pure ()
  | _ => pure ()
  let ctorTyWithInd : Ty (numParams + 1) := Ty.pis fieldTys retTy
  let ctorTy : Ty numParams := ctorTyWithInd.subst (Subst.beta (.const indName indUnivs))
  return (ctorName, ctorTy)

end Qdt
