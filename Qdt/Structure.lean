import Qdt.Bidirectional
import Qdt.Control
import Qdt.Frontend.Ast
import Qdt.Inductive
import Qdt.Nbe
import Qdt.Params
import Qdt.Quote

namespace Qdt

open Lean (Name)
open Frontend (Ast)

structure StructureField where
  name : Name
  params : List Ast
  ty : Ast

structure Structure where
  name : Name
  univParams : List Name
  params : List Ast
  tyOpt : Option Ast
  fields : List StructureField

private def parseStructureField (ast : Ast) : Option StructureField :=
  match ast with
  | .node `StructureField #[.ident name, .node `null paramsAst, ty] =>
      some { name, params := paramsAst.toList, ty }
  | _ => none

def parseStructure (ast : Ast) : Option Structure :=
  match ast with
  | .node `Command.structure #[.ident name, .node `null univParamsAst, .node `null paramsAst, tyOpt, .node `null fieldsAst] =>
      let univParams := univParamsAst.toList.filterMap fun a => match a with | .ident n => some n | _ => none
      let tyOpt := if tyOpt.kind? == some `null || tyOpt == .missing then none else some tyOpt
      let fields := fieldsAst.toList.filterMap parseStructureField
      some { name, univParams, params := paramsAst.toList, tyOpt, fields }
  | _ => none

private def mkFieldTyAst (field : StructureField) : Ast :=
  field.params.foldr (fun b acc => .node `Term.pi #[b, acc]) field.ty

private def getAtomicFieldString (structName : Name) (fieldName : Name) : CoreM String := do
  let .str .anonymous s := fieldName
    | throw (.msg s!"{structName}: field name must be atomic")
  return s

private def mkParamEnv : (numParams : Nat) → Env (numParams + 1) numParams
  | 0 => .nil
  | numParams + 1 => Env.cons (VTm.varAt numParams) (mkParamEnv numParams).weaken

private def mkPrevEnv
    (structName : Name)
    (numParams : Nat)
    (univs : List Universe)
    (params : List (VTm (numParams + 1)))
    (x : VTm (numParams + 1)) :
    {b : Nat} → Ctx numParams b → MetaM (Env (numParams + 1) b)
  | _, .nil => return mkParamEnv numParams
  | _, .snoc fs ⟨name, _⟩ => do
      let envTail ← mkPrevEnv structName numParams univs params x fs
      let fname ← getAtomicFieldString structName name
      let projName := structName.str fname
      let proj : VTm (numParams + 1) := VTm.const projName univs
      let proj ← proj.apps params
      let proj ← proj.app x
      return Env.cons proj envTail

def elabStructure (info : Structure) : MetaM Unit := do
  let numParams := info.params.length

  let (paramCtx, paramTys) ← withChild 2 (elabParams info.params)
  let resultTy : Ty numParams ←
    match info.tyOpt with
    | none => pure (Ty.u .zero)
    | some ty =>
        match ty with
        | .node `Term.u #[astLevel] =>
            let level ← withChild 3 (withChild 0 (checkAstUniverse astLevel))
            pure (Ty.u level : Ty numParams)
        | _ => throw (.structureResultTypeMustBeTypeUniverse info.name)

  let _structFieldStrs ← info.fields.mapM fun f => getAtomicFieldString info.name f.name
  let ctorFieldBinders : List Ast :=
    info.fields.map fun f => .node `Binder.typed #[.ident f.name, mkFieldTyAst f]

  let indSynth : Inductive :=
    {
      name := info.name
      univParams := info.univParams
      params := info.params
      tyOpt := info.tyOpt
      ctors :=
        [
          {
            name := `mk
            fields := ctorFieldBinders
            tyOpt := none
          }
        ]
    }
  Qdt.elabInductive indSynth

  let (_fieldCtx, fieldTele) ← elabParamsFrom ctorFieldBinders paramCtx

  let np1 := numParams + 1
  let numFields := ctorFieldBinders.length
  let numParamsFields := numParams + numFields

  let paramsVal : List (VTm numParams) :=
    List.finRange numParams |>.map fun i => VTm.varAt i.val

  let x : VTm np1 := VTm.varAt numParams

  let univParams := (← getThe MetaState).univParams
  let structUnivs := univParams.map Universe.level
  let majorTy : VTm numParams := VTm.const info.name structUnivs
  let majorTy ← majorTy.apps paramsVal
  let majorTy ← majorTy.quote
  let majorTy : Ty numParams := Ty.el majorTy

  let rec goProj
      {b}
      (hb : b ≤ numParamsFields) :
      Ctx numParams b →
      MetaM Unit
    | .nil => return
    | .snoc (b := idx) fs ⟨name, ty⟩ => do
        goProj (Nat.le_of_succ_le hb) fs

        let fname ← getAtomicFieldString info.name name
        let projName := info.name.str fname

        let envPrev ← mkPrevEnv info.name numParams structUnivs (weaken paramsVal) x fs
        let fty : Ty idx := ty
        let ftyVal ← fty.eval envPrev
        let ftyTy ← ftyVal.quote

        let pVar : Tm np1 := Tm.var ⟨0, by omega⟩
        let fieldIdx := idx - numParams
        let projBody : Tm np1 := Tm.proj fieldIdx pVar

        let projBodyTy : Ty numParams := Ty.pi ⟨`p, majorTy⟩ ftyTy
        let projTy : Ty 0 := Ty.pis paramTys projBodyTy
        let projTm : Tm 0 :=
          Tm.lams paramTys <|
          Tm.lam ⟨`p, majorTy⟩ projBody

        let univParams := (← getThe MetaState).univParams
        let _ ← Global.addEntry projName (.definition { univParams, ty := projTy, tm := projTm })

  goProj (Nat.le_refl numParamsFields) fieldTele

end Qdt
