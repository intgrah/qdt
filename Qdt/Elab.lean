module

public import Qdt.Structure

public section

namespace Qdt

open Lean (Name)
open Frontend (Ast Path)

variable (q₀ : Key)

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

def Definition.elab (d : Definition) : OptionT (ElabM q₀) Unit := do
  if let some e := checkDuplicateUnivParams d.univParams then
    raiseError q₀ e
  let (paramCtx, paramTys) ← withChild q₀ 2 (Params.elab q₀ d.params)
  let (tm, ty) ←
    match d.tyOpt with
    | none =>
        let (tm, tyVal) ← withChild q₀ 4 (inferTm q₀ paramCtx d.body)
        let ty ← tyVal.quote q₀
        pure (tm, ty)
    | some tyRaw =>
        let ty ← OptionT.lift (withChild q₀ 3 (checkTy q₀ paramCtx tyRaw))
        let tyVal ← ty.eval q₀ paramCtx.env
        let tm ← OptionT.lift (withChild q₀ 4 (checkTm q₀ paramCtx tyVal d.body))
        pure (tm, ty)
  withChild q₀ 0 (emitHover q₀ (.signature d.name paramTys ty))
  let tm := Tm.lams paramTys tm
  let ty := Ty.pis paramTys ty
  let _ ← addConstant q₀ d.name (.definition { numUnivParams := d.univParams.length, ty, tm })

def Example.elab (e : Example) : OptionT (ElabM q₀) Unit := do
  if let some err := checkDuplicateUnivParams e.univParams then
    raiseError q₀ err
  let (paramCtx, _paramTys) ← withChild q₀ 0 (Params.elab q₀ e.params)
  match e.tyOpt with
  | some tyRaw =>
      let expected ← OptionT.lift (withChild q₀ 1 (checkTy q₀ paramCtx tyRaw))
      let expected ← expected.eval q₀ paramCtx.env
      let _term ← OptionT.lift (withChild q₀ 2 (checkTm q₀ paramCtx expected e.body))
  | none =>
      let (_term, _tyVal) ← withChild q₀ 2 (inferTm q₀ paramCtx e.body)

def Axiom.elab (a : Axiom) : OptionT (ElabM q₀) Unit := do
  if let some err := checkDuplicateUnivParams a.univParams then
    raiseError q₀ err
  let (paramCtx, paramTys) ← withChild q₀ 2 (Params.elab q₀ a.params)
  let ty ← OptionT.lift (withChild q₀ 3 (checkTy q₀ paramCtx a.ty))
  withChild q₀ 0 (emitHover q₀ (.signature a.name paramTys ty))
  let ty := Ty.pis paramTys ty
  let _ ← addConstant q₀ a.name (.axiom { numUnivParams := a.univParams.length, ty })

def Inductive.elab (info : Inductive) : OptionT (ElabM q₀) Unit := do
  if let some err := checkDuplicateUnivParams info.univParams then
    raiseError q₀ err
  let result ← Inductive.elab' q₀ info
  let _ ← result.ctorEntries.foldlM (init := 0) fun i (ctorName, ctorConst) => do
    withChild q₀ (4 + i) (emitHover q₀ (.signature ctorName .nil ctorConst.ty))
    return i + 1

def Structure.elab (info : Structure) : OptionT (ElabM q₀) Unit := do
  if let some err := checkDuplicateUnivParams info.univParams then
    raiseError q₀ err
  let _ ← Structure.elab' q₀ info

end Qdt
