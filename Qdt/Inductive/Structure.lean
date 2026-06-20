module

public import Qdt.Inductive.Core
import Qdt.Bidirectional
import Qdt.Params

public section

namespace Qdt

open Lean (Name)
open Frontend (Ast Path)

variable (q₀ : Key)

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

def getAtomicFieldString (structName : Name) (fieldName : Name) : OptionT (ElabM q₀) String := do
  let .str .anonymous s := fieldName
    | raiseError q₀ (.fieldNameNotAtomic structName)
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
    {b : Nat} → Ctx numParams b → OptionT (ElabM q₀) (Env (numParams + 1) b)
  | _, .nil => return mkParamEnv numParams
  | _, .snoc fs ⟨name, _, _⟩ => do
      let envTail ← mkPrevEnv structName numParams univs params x fs
      let fname ← getAtomicFieldString q₀ structName name
      let projName := structName.str fname
      let ne : Neutral (numParams + 1) := ⟨.const projName univs, .nil⟩
      let ne := params.foldl Neutral.app ne
      let ne := ne.app x
      return Env.cons (.neutral ne) envTail

def checkFields {m} (ctx : TermContext m) : List StructureField → Nat → OptionT (ElabM q₀) Unit
  | [], _ => return ()
  | field :: rest, j => do
    let (fieldParamCtx, fieldParamTele) ←
      withChild q₀ (4 + j) (withChild q₀ 1 (Params.elabFrom q₀ ctx field.params))
    let fieldRetTy ← OptionT.lift (withChild q₀ (4 + j) (withChild q₀ 2 (checkTy q₀ fieldParamCtx field.ty)))
    OptionT.lift (resumePostponed q₀ true)
    let fullFieldTy := Ty.pis fieldParamTele fieldRetTy
    let fullFieldTyVal ← fullFieldTy.eval q₀ ctx.env
    checkFields (← ctx.bindV q₀ field.name fullFieldTyVal) rest (j + 1)

public structure StructureResult (numParams : Nat) : Type where
  indResult : InductiveResult numParams
  projEntries : List (Name × Constant)

public def Structure.elab' (info : Structure) :
    OptionT (ElabM q₀) (StructureResult info.params.length) := do
  let numParams := info.params.length

  let (paramCtx, paramTys) ← withChild q₀ 2 (Params.elab q₀ info.params)
  let resultTy : Ty numParams ←
    match info.tyOpt with
    | none => pure (Ty.u .zero)
    | some ty =>
        match ty with
        | .node `Term.u cs =>
            let level ← withChild q₀ 3 (checkAstUniverse q₀ cs[0]!)
            pure (Ty.u level : Ty numParams)
        | _ => raiseError q₀ (Error.structureResultTypeMustBeTypeUniverse info.name)

  let _structFieldStrs ← info.fields.mapM fun field => getAtomicFieldString q₀ info.name field.name
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
  OptionT.lift (withChild q₀ 0 (emitHover q₀ (.signature info.name paramTys resultTy)))
  let suppressHovers {α} : OptionT (ElabM q₀) α → OptionT (ElabM q₀) α :=
    ReaderT.adapt (fun ctx : ElabContext => { ctx with collectHovers := false })
  let indResult ← suppressHovers (Inductive.elab' q₀ indSynth)

  let some (_, ctorTy) := indResult.ctorTys.head?
    | failure
  let ⟨_fieldTeleEnd, fieldTele, _retTy⟩ := ctorTy.getTele

  let paramTys : Ctx 0 info.params.length ←
    paramTys.mapM fun (n, bi, t) => return (n, bi, ← t.zonk q₀)
  let paramFreeMVars : List UMVarId :=
    let rec go {a b : Nat} : Ctx a b → List UMVarId
      | .nil => []
      | .snoc rest (_, _, t) => go rest ++ t.freeUMVars
    go paramTys
  let indFreeMVars :=
    paramFreeMVars ++
    indResult.indEntry.snd.freeUMVars ++
    indResult.recEntry.snd.freeUMVars ++
    indResult.ctorEntries.flatMap (fun (_, c) => c.freeUMVars)
  let (promotedNames, subst) :=
    promoteUniverseMVars indResult.recEntry.snd.toConstantInfo.univParams indFreeMVars
  let structUnivParams := info.univParams ++ promotedNames
  let extras : List Universe := promotedNames.map Universe.param
  let indName := info.name
  let recName := info.recName
  let ctorName := info.name.str "mk"
  let extendAll (c : Constant) : Constant :=
    let c := c.extendConstUnivs extras indName
    let c := c.extendConstUnivs extras recName
    c.extendConstUnivs extras ctorName
  let updateConst (c : Constant) : Constant :=
    let c := c.substUMVars subst
    let c := extendAll c
    c.setUnivParams (c.toConstantInfo.univParams ++ promotedNames)
  let indEntry := (indResult.indEntry.fst, updateConst indResult.indEntry.snd)
  let recEntry := (indResult.recEntry.fst, updateConst indResult.recEntry.snd)
  let ctorEntries := indResult.ctorEntries.map fun (n, c) => (n, updateConst c)
  addPending q₀ indEntry.fst indEntry.snd
  addPending q₀ recEntry.fst recEntry.snd
  for (cname, cconst) in ctorEntries do
    addPending q₀ cname cconst
  let indResult : InductiveResult numParams :=
    { indEntry, ctorEntries, recEntry, ctorTys := indResult.ctorTys }
  let fieldTele := fieldTele.map (fun (n, bi, t) => (n, bi, Ty.substUMVars subst t))
  let paramTys : Ctx 0 info.params.length :=
    paramTys.map fun (n, bi, t) => (n, bi, Ty.substUMVars subst t)

  checkFields q₀ paramCtx info.fields 0

  let np1 := numParams + 1
  let numFields := ctorFieldBinders.length
  let numParamsFields := numParams + numFields

  let paramsVal : List (VTm numParams) :=
    List.finRange numParams |>.map fun i => VTm.varAt i.val

  let x : VTm np1 := VTm.varAt numParams

  let structUnivs := structUnivParams.map Universe.param
  let majorTy : VTm numParams := VTm.const info.name structUnivs
  let majorTy ← majorTy.apps q₀ paramsVal
  let majorTy ← majorTy.quote q₀
  let majorTy : Ty numParams := Ty.el majorTy

  let rec goProj
      {b : Nat}
      (acc : List (Name × Constant)) :
      Ctx numParams b →
      OptionT (ElabM q₀) (List (Name × Constant))
    | .nil => return acc
    | .snoc (b := idx) fs ⟨name, _, ty⟩ => do
        let acc ← goProj acc fs

        let fname ← getAtomicFieldString q₀ info.name name
        let projName := info.name.str fname

        let envPrev ← mkPrevEnv q₀ info.name numParams structUnivs (weaken paramsVal) x fs
        let fty : Ty idx := ty
        let ftyVal ← fty.eval q₀ envPrev
        let ftyTy ← ftyVal.quote q₀

        let pVar : Tm np1 := Tm.var ⟨0, by omega⟩
        let fieldIdx := idx - numParams
        let projBody : Tm np1 := Tm.proj fieldIdx pVar

        let projBodyTy : Ty numParams := Ty.pi `self .explicit majorTy ftyTy
        let projTy : Ty 0 := Ty.pis paramTys.toImplicit projBodyTy
        let projTm : Tm 0 :=
          Tm.lams paramTys.toImplicit <|
          Tm.lam `self .explicit majorTy projBody

        let projTy ← projTy.zonk q₀
        let projTm ← projTm.zonk q₀
        let projTy := projTy.substUMVars subst
        let projTm := projTm.substUMVars subst
        let entry : Name × Constant := (projName, .definition { univParams := structUnivParams, ty := projTy, tm := projTm })
        addPending q₀ projName entry.2
        withChild q₀ (4 + fieldIdx) (emitHover q₀ (.signature projName (paramTys.toImplicit.snoc ⟨`self, .explicit, majorTy⟩) ftyTy))
        return acc ++ [entry]

  let projEntries ← goProj [] fieldTele
  return { indResult, projEntries }

end Qdt
