module

public import Qdt.Bidirectional
public import Qdt.Control
public import Qdt.Frontend.Ast

@[expose] public section

namespace Qdt

open Lean (Name)
open Frontend (Ast Path)

def getTypedBinder : Ast → Option (Name × Ast)
  | .node `Binder.typed cs => some (cs[0]!.getName, cs[1]!)
  | _ => none

def elabParamsWithLevels {n : Nat} (ctx : TermContext n) (params : List Ast) :
    OptionT MetaM (TermContext (n + params.length) × Ctx n (n + params.length) × List Universe) :=
  Nat.zero_add params.length ▸ go n 0 ctx .nil [] params
  where
    go {a : Nat} (b : Nat) (idx : Nat) (ctx : TermContext b) (acc : Ctx a b) (levels : List Universe) :
      (params : List Ast) →
        OptionT MetaM (TermContext (b + params.length) × Ctx a (b + params.length) × List Universe)
    | [] => return (ctx, acc, levels.reverse)
    | ast :: bs => do
        let some (name, tyAst) := getTypedBinder ast
          | raiseError .syntaxError
        let (ty, level) ← withChild idx (withChild 1 (checkTyWithLevel ctx tyAst))
        let tyVal ← ty.eval ctx.env
        withChild idx (withChild 0 (emitType ctx tyVal))
        let ctx := ctx.bind name tyVal
        let ih ← go (b + 1) (idx + 1) ctx (acc.snoc ⟨name, ty⟩) (level :: levels) bs
        return by simpa only [List.length_cons, Nat.add_comm bs.length, Nat.add_assoc b] using ih

def elabParamsFrom {n : Nat} (ctx : TermContext n) (params : List Ast) :
    OptionT MetaM (TermContext (n + params.length) × Ctx n (n + params.length)) := do
  let (ctx, tele, _) ← elabParamsWithLevels ctx params
  return (ctx, tele)

def elabParams (params : List Ast) :
    OptionT MetaM (TermContext params.length × Ctx 0 params.length) :=
  Nat.zero_add params.length ▸ elabParamsFrom TermContext.empty params

def elabVParamsFrom {n : Nat} (ctx : TermContext n) (params : List Ast) :
    OptionT MetaM (TermContext (n + params.length) × Tele VParam n (n + params.length)) :=
  Nat.zero_add params.length ▸ go n 0 ctx .nil params
  where
    go {a : Nat} (b : Nat) (idx : Nat) (ctx : TermContext b) (acc : Tele VParam a b) :
      (params : List Ast) →
      OptionT MetaM (TermContext (b + params.length) × Tele VParam a (b + params.length))
    | [] => return (ctx, acc)
    | ast :: bs => do
        let some (name, tyAst) := getTypedBinder ast
          | raiseError .syntaxError
        let ty ← withChild idx (withChild 1 (checkTy ctx tyAst))
        let tyVal ← ty.eval ctx.env
        withChild idx (withChild 0 (emitType ctx tyVal))
        let ctx := ctx.bind name tyVal
        let ih ← go (b + 1) (idx + 1) ctx (acc.snoc ⟨name, tyVal⟩) bs
        return by simpa only [List.length_cons, Nat.add_comm bs.length, Nat.add_assoc b] using ih

def elabVParams (params : List Ast) :
    OptionT MetaM (TermContext params.length × Tele VParam 0 params.length) := by
  simpa only [Nat.zero_add] using elabVParamsFrom TermContext.empty params

end Qdt
