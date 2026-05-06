module

public import Qdt.Inductive

public section

namespace Qdt

open Lean (Name)
open Frontend (Ast Path)

variable (ι₀ : ∀ i, InputV i) (q₀ : Key)

public structure StructureField where
  name : Name
  params : List Ast
  ty : Ast

public structure Structure where
  name : Name
  mkName : Name
  recName : Name
  univParams : List Name
  params : List Ast
  tyOpt : Option Ast
  fields : List StructureField

def StructureField.parse : Ast → Option StructureField
  | .node `StructureField cs =>
      let name := cs[0]!.getName
      let paramsNode := cs[1]!
      let ty := cs[2]!
      let params := match paramsNode with
        | .node _ cs => cs.toList
        | _ => []
      some { name, params, ty }
  | _ => none

public def Structure.parse : Ast → Option Structure
  | .node `Command.structure cs =>
      let name := cs[0]!.getName
      let univParamsNode := cs[1]!
      let paramsNode := cs[2]!
      let tyOpt := cs[3]!
      let fieldsNode := cs[4]!
      let univParams := match univParamsNode with
        | .node _ cs => cs.toList.filterMap fun c => c.name?
        | _ => []
      let params := match paramsNode with
        | .node _ cs => cs.toList
        | _ => []
      let tyOpt : Option Ast :=
        if tyOpt.kind? == some `null || (match tyOpt with | .missing => true | _ => false)
        then none else some tyOpt
      let fields := match fieldsNode with
        | .node _ cs => cs.toList.filterMap StructureField.parse
        | _ => []
      some { name, mkName := name.str "mk", recName := name.str "rec", univParams, params, tyOpt, fields }
  | _ => none

def mkFieldTyAst (field : StructureField) : Ast :=
  field.params.foldr (fun b acc => .node `Term.pi #[b, acc]) field.ty

def getAtomicFieldString (structName : Name) (fieldName : Name) : OptionT (ElabM ι₀ q₀) String := do
  let .str .anonymous s := fieldName
    | raiseError ι₀ q₀ (.fieldNameNotAtomic structName)
  return s

def mkParamEnv : (numParams : Nat) → Env (numParams + 1) numParams
  | 0 => .nil
  | numParams + 1 => Env.cons (VTm.varAt numParams) (mkParamEnv numParams).weaken

def mkPrevEnv
    (structName : Name)
    (numParams : Nat)
    (univs : List Universe)
    (params : List (VTm (numParams + 1)))
    (x : VTm (numParams + 1)) :
    {b : Nat} → Ctx numParams b → OptionT (ElabM ι₀ q₀) (Env (numParams + 1) b)
  | _, .nil => return mkParamEnv numParams
  | _, .snoc fs ⟨name, _⟩ => do
      let envTail ← mkPrevEnv structName numParams univs params x fs
      let fname ← getAtomicFieldString ι₀ q₀ structName name
      let projName := structName.str fname
      let ne : Neutral (numParams + 1) := ⟨.const projName univs, .nil⟩
      let ne := params.foldl Neutral.app ne
      let ne := ne.app x
      return Env.cons (.neutral ne) envTail

def checkFields {m} (ctx : TermContext m) : List StructureField → Nat → OptionT (ElabM ι₀ q₀) Unit
  | [], _ => return ()
  | field :: rest, j => do
    let (fieldParamCtx, fieldParamTele) ←
      withChild ι₀ q₀ (4 + j) (withChild ι₀ q₀ 1 (Params.elabFrom ι₀ q₀ ctx field.params))
    let fieldRetTy ← OptionT.lift (withChild ι₀ q₀ (4 + j) (withChild ι₀ q₀ 2 (checkTy ι₀ q₀ fieldParamCtx field.ty)))
    let fullFieldTy := Ty.pis fieldParamTele fieldRetTy
    let fullFieldTyVal ← fullFieldTy.eval ι₀ q₀ ctx.env
    checkFields (ctx.bind field.name fullFieldTyVal) rest (j + 1)

public structure StructureResult where
  indResult : InductiveResult
  projEntries : List (Name × Constant)

public def Structure.elab' (info : Structure) : OptionT (ElabM ι₀ q₀) StructureResult := do
  let numParams := info.params.length

  let (paramCtx, paramTys) ← withChild ι₀ q₀ 2 (Params.elab ι₀ q₀ info.params)
  let resultTy : Ty numParams ←
    match info.tyOpt with
    | none => pure (Ty.u .zero)
    | some ty =>
        match ty with
        | .node `Term.u cs =>
            let level ← withChild ι₀ q₀ 3 (checkAstUniverse ι₀ q₀ cs[0]!)
            pure (Ty.u level : Ty numParams)
        | _ => raiseError ι₀ q₀ (Error.structureResultTypeMustBeTypeUniverse info.name)

  let _structFieldStrs ← info.fields.mapM fun field => getAtomicFieldString ι₀ q₀ info.name field.name
  let ctorFieldBinders : List Ast :=
    info.fields.map fun field => .node `Binder.typed #[.ident field.name, mkFieldTyAst field]

  let indSynth : Inductive :=
    {
      name := info.name
      recName := info.recName
      univParams := info.univParams
      params := info.params
      tyOpt := info.tyOpt
      ctors := [⟨`mk, ctorFieldBinders, none⟩]
    }
  OptionT.lift (withChild ι₀ q₀ 0 (emitHover ι₀ q₀ (.signature info.name paramTys resultTy)))
  let suppressHovers {α} : OptionT (ElabM ι₀ q₀) α → OptionT (ElabM ι₀ q₀) α :=
    ReaderT.adapt (fun ctx : ElabContext => { ctx with collectHovers := false })
  let indResult ← suppressHovers (Inductive.elab' ι₀ q₀ indSynth)

  let (_fieldCtx, fieldTele) ← suppressHovers (Params.elabFrom ι₀ q₀ paramCtx ctorFieldBinders)

  checkFields ι₀ q₀ paramCtx info.fields 0

  let np1 := numParams + 1
  let numFields := ctorFieldBinders.length
  let numParamsFields := numParams + numFields

  let paramsVal : List (VTm numParams) :=
    List.finRange numParams |>.map fun i => VTm.varAt i.val

  let x : VTm np1 := VTm.varAt numParams

  let univParams ← getUnivParams ι₀ q₀
  let structUnivs := univParams.map Universe.level
  let majorTy : VTm numParams := VTm.const info.name structUnivs
  let majorTy ← majorTy.apps ι₀ q₀ paramsVal
  let majorTy ← majorTy.quote ι₀ q₀
  let majorTy : Ty numParams := Ty.el majorTy

  let rec goProj
      {b : Nat}
      (hb : b ≤ numParamsFields)
      (acc : List (Name × Constant)) :
      Ctx numParams b →
      OptionT (ElabM ι₀ q₀) (List (Name × Constant))
    | .nil => return acc
    | .snoc (b := idx) fs ⟨name, ty⟩ => do
        let acc ← goProj (Nat.le_of_succ_le hb) acc fs

        let fname ← getAtomicFieldString ι₀ q₀ info.name name
        let projName := info.name.str fname

        let envPrev ← mkPrevEnv ι₀ q₀ info.name numParams structUnivs (weaken paramsVal) x fs
        let fty : Ty idx := ty
        let ftyVal ← fty.eval ι₀ q₀ envPrev
        let ftyTy ← ftyVal.quote ι₀ q₀

        let pVar : Tm np1 := Tm.var ⟨0, by omega⟩
        let fieldIdx := idx - numParams
        let projBody : Tm np1 := Tm.proj fieldIdx pVar

        let projBodyTy : Ty numParams := Ty.pi `self majorTy ftyTy
        let projTy : Ty 0 := Ty.pis paramTys projBodyTy
        let projTm : Tm 0 :=
          Tm.lams paramTys <|
          Tm.lam `self majorTy projBody

        let univParams ← getUnivParams ι₀ q₀
        let projVtm ← projTm.eval ι₀ q₀ .nil
        let entry : Name × Constant := (projName, .definition { univParams, ty := projTy, tm := projTm, vtm := projVtm })
        let _ ← addConstant ι₀ q₀ projName entry.2
        withChild ι₀ q₀ (4 + fieldIdx) (emitHover ι₀ q₀ (.signature projName (paramTys.snoc ⟨`self, majorTy⟩) ftyTy))
        return acc ++ [entry]

  let projEntries ← goProj (Nat.le_refl numParamsFields) [] fieldTele
  return { indResult, projEntries }

end Qdt
