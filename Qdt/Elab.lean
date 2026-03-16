module

public import Qdt.Structure

public section

namespace Qdt

open Lean (Name)
open Frontend (Ast Path)

variable (ι₀ : ∀ i, InputV i) (q₀ : Key)

structure Import where
  moduleName : Name

def Import.parse : Ast → Option Import
  | .node `Command.import cs =>
      if cs.size != 1 then none else
      some { moduleName := cs[0]!.getName }
  | _ => none

structure Definition where
  name : Name
  univParams : List Name
  params : List Ast
  tyOpt : Option Ast
  body : Ast

structure Example where
  univParams : List Name
  params : List Ast
  tyOpt : Option Ast
  body : Ast

structure Axiom where
  name : Name
  univParams : List Name
  params : List Ast
  ty : Ast

def Definition.parse : Ast → Option Definition
  | .node `Command.definition cs =>
      if cs.size != 5 then none else
      let name := cs[0]!.getName
      let univParamsAst := cs[1]!
      let paramsAst := cs[2]!
      let tyOpt := cs[3]!
      let body := cs[4]!
      let univParams := match univParamsAst with
        | .node _ cs => cs.toList.filterMap fun c => c.name?
        | _ => []
      let tyOpt : Option Ast :=
        if tyOpt.kind? == some `null || (match tyOpt with | .missing => true | _ => false)
        then none else some tyOpt
      let params := match paramsAst with
        | .node _ cs => cs.toList
        | _ => []
      some { name, univParams, params, tyOpt, body }
  | _ => none

def Example.parse : Ast → Option Example
  | .node `Command.example cs =>
      if cs.size != 3 then none else
      let paramsAst := cs[0]!
      let tyOpt := cs[1]!
      let body := cs[2]!
      let tyOpt : Option Ast :=
        if tyOpt.kind? == some `null || (match tyOpt with | .missing => true | _ => false)
        then none else some tyOpt
      let params := match paramsAst with
        | .node _ cs => cs.toList
        | _ => []
      some { univParams := [], params, tyOpt, body }
  | _ => none

def Axiom.parse : Ast → Option Axiom
  | .node `Command.axiom cs =>
      if cs.size != 4 then none else
      let name := cs[0]!.getName
      let univParamsAst := cs[1]!
      let paramsAst := cs[2]!
      let ty := cs[3]!
      let univParams := match univParamsAst with
        | .node _ cs => cs.toList.filterMap fun c => c.name?
        | _ => []
      let params := match paramsAst with
        | .node _ cs => cs.toList
        | _ => []
      some { name, univParams, params, ty }
  | _ => none

def checkDuplicateUnivParams (params : List Name) : Option Error :=
  let rec loop (seen : Std.HashSet Name) : List Name → Option Error
    | [] => none
    | n :: ns =>
        if n ∈ seen then
          some (.duplicateUniverseParam n)
        else
          loop (seen.insert n) ns
  loop ∅ params

def Definition.elab (d : Definition) : OptionT (ElabM ι₀ q₀) Unit := do
  if let some e := checkDuplicateUnivParams d.univParams then
    raiseError ι₀ q₀ e
  let (paramCtx, paramTys) ← withChild ι₀ q₀ 2 (Params.elab ι₀ q₀ d.params)
  let (tm, ty) ←
    match d.tyOpt with
    | none =>
        let (tm, tyVal) ← withChild ι₀ q₀ 4 (inferTm ι₀ q₀ paramCtx d.body)
        let ty ← tyVal.quote ι₀ q₀
        pure (tm, ty)
    | some tyRaw =>
        let ty ← OptionT.lift (withChild ι₀ q₀ 3 (checkTy ι₀ q₀ paramCtx tyRaw))
        let tyVal ← ty.eval ι₀ q₀ paramCtx.env
        let tm ← OptionT.lift (withChild ι₀ q₀ 4 (checkTm ι₀ q₀ paramCtx tyVal d.body))
        pure (tm, ty)
  withChild ι₀ q₀ 0 (emitHover ι₀ q₀ (.signature d.name paramTys ty))
  let tm := Tm.lams paramTys tm
  let ty := Ty.pis paramTys ty
  let _ ← addConstant ι₀ q₀ d.name (.definition { univParams := d.univParams, ty, tm })

def Example.elab (e : Example) : OptionT (ElabM ι₀ q₀) Unit := do
  if let some err := checkDuplicateUnivParams e.univParams then
    raiseError ι₀ q₀ err
  let (paramCtx, _paramTys) ← withChild ι₀ q₀ 0 (Params.elab ι₀ q₀ e.params)
  match e.tyOpt with
  | some tyRaw =>
      let expected ← OptionT.lift (withChild ι₀ q₀ 1 (checkTy ι₀ q₀ paramCtx tyRaw))
      let expected ← expected.eval ι₀ q₀ paramCtx.env
      let _term ← OptionT.lift (withChild ι₀ q₀ 2 (checkTm ι₀ q₀ paramCtx expected e.body))
  | none =>
      let (_term, _tyVal) ← withChild ι₀ q₀ 2 (inferTm ι₀ q₀ paramCtx e.body)

def Axiom.elab (a : Axiom) : OptionT (ElabM ι₀ q₀) Unit := do
  if let some err := checkDuplicateUnivParams a.univParams then
    raiseError ι₀ q₀ err
  let (paramCtx, paramTys) ← withChild ι₀ q₀ 2 (Params.elab ι₀ q₀ a.params)
  let ty ← OptionT.lift (withChild ι₀ q₀ 3 (checkTy ι₀ q₀ paramCtx a.ty))
  withChild ι₀ q₀ 0 (emitHover ι₀ q₀ (.signature a.name paramTys ty))
  let ty := Ty.pis paramTys ty
  let _ ← addConstant ι₀ q₀ a.name (.axiom { univParams := a.univParams, ty })

def Inductive.elab (info : Inductive) : OptionT (ElabM ι₀ q₀) Unit := do
  if let some err := checkDuplicateUnivParams info.univParams then
    raiseError ι₀ q₀ err
  let result ← Inductive.elab' ι₀ q₀ info
  let _ ← result.ctorEntries.foldlM (init := 0) fun i (ctorName, ctorConst) => do
    withChild ι₀ q₀ (4 + i) (emitHover ι₀ q₀ (.signature ctorName .nil ctorConst.ty))
    return i + 1

def Structure.elab (info : Structure) : OptionT (ElabM ι₀ q₀) Unit := do
  if let some err := checkDuplicateUnivParams info.univParams then
    raiseError ι₀ q₀ err
  let _ ← Structure.elab' ι₀ q₀ info

end Qdt
