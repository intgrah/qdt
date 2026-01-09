import Qdt.Control
import Qdt.Frontend.Ast
import Qdt.Inductive
import Qdt.Nbe
import Qdt.Params
import Qdt.Quote

namespace Qdt

open Lean (Name)

private def mkFieldTyTerm (field : Frontend.Ast.Command.StructureField) : Frontend.Ast.Term :=
  field.params.foldr (fun b acc => .pi b.src b acc) field.ty

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
    (params : List (VTm (numParams + 1)))
    (x : VTm (numParams + 1)) :
    {b : Nat} → Tele Param numParams b → MetaM (Env (numParams + 1) b)
  | _, .nil => return mkParamEnv numParams
  | _, .snoc fs ⟨name, _⟩ => do
      let envTail ← mkPrevEnv structName numParams params x fs
      let fname ← getAtomicFieldString structName name
      let projName := structName.str fname
      let proj : VTm (numParams + 1) := VTm.const projName
      let proj ← proj.apps params
      let proj ← proj.app x
      return Env.cons proj envTail

def elabStructure (info : Frontend.Ast.Command.Structure) : MetaM Unit := do
  let numParams := info.params.length

  let (paramCtx, paramTys) ← elabParams info.params
  let resultTy : Ty numParams ←
    match info.tyOpt with
    | none => pure (Ty.u : Ty numParams)
    | some (.u _) => pure Ty.u
    | some _ => throw (.structureResultTypeMustBeType info.src info.name)

  let structFieldStrs ← info.fields.mapM fun f => getAtomicFieldString info.name f.name
  let ctorFieldBinders : List Frontend.Ast.TypedBinder :=
    info.fields.map fun f => ⟨f.src, f.name, mkFieldTyTerm f⟩

  let indSynth : Frontend.Ast.Command.Inductive :=
    {
      src := info.src
      name := info.name
      params := info.params
      tyOpt := info.tyOpt
      ctors :=
        [
          {
            src := info.src
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

  let majorTy : VTm numParams := VTm.const info.name
  let majorTy ← majorTy.apps paramsVal
  let majorTy ← majorTy.quote
  let majorTy : Ty numParams := Ty.el majorTy

  let rec goProj
      {b}
      (hb : b ≤ numParamsFields) :
      Tele Param numParams b →
      MetaM Unit
    | .nil => return
    | .snoc (b := idx) fs ⟨name, ty⟩ => do
        goProj (Nat.le_of_succ_le hb) fs

        let fname ← getAtomicFieldString info.name name
        let projName := info.name.str fname

        let envPrev ← mkPrevEnv info.name numParams (weaken paramsVal) x fs
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

        Global.addEntry projName (.definition ⟨projTy, projTm⟩)

  goProj (Nat.le_refl numParamsFields) fieldTele

end Qdt
