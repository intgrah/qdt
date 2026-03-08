module

public import Qdt.Bidirectional

@[expose] public section

namespace Qdt

open Lean (Name)
open Frontend (Ast Path)

def getTypedBinder : Ast → Option (Name × Ast)
  | .node `Binder.typed cs => some (cs[0]!.getName, cs[1]!)
  | _ => none

def Params.elabWithLevels {n : Nat} (ctx : TermContext n) (params : List Ast) :
    OptionT ElabM (TermContext (n + params.length) × Ctx n (n + params.length) × List Universe) :=
  Nat.zero_add params.length ▸ go n 0 ctx .nil [] params
  where
    go {a : Nat} (b : Nat) (idx : Nat) (ctx : TermContext b) (acc : Ctx a b) (levels : List Universe) :
      (params : List Ast) →
        OptionT ElabM (TermContext (b + params.length) × Ctx a (b + params.length) × List Universe)
    | [] => return (ctx, acc, levels.reverse)
    | ast :: bs => do
        let some (name, tyAst) := getTypedBinder ast
          | failure
        let (ty, level) ← OptionT.lift (withChild idx (withChild 1 (checkTyWithLevel ctx tyAst)))
        let tyVal ← ty.eval ctx.env
        let tyQuoted ← tyVal.quote
        withChild idx (withChild 0 (emitHover (.localVar name ctx.names tyQuoted)))
        let ctx := ctx.bind name tyVal
        let ih ← go (b + 1) (idx + 1) ctx (acc.snoc ⟨name, ty⟩) (level :: levels) bs
        return by simpa only [List.length_cons, Nat.add_comm bs.length, Nat.add_assoc b] using ih

def Params.elabFrom {n : Nat} (ctx : TermContext n) (params : List Ast) :
    OptionT ElabM (TermContext (n + params.length) × Ctx n (n + params.length)) := do
  let (ctx, tele, _) ← elabWithLevels ctx params
  return (ctx, tele)

def Params.elab (params : List Ast) :
    OptionT ElabM (TermContext params.length × Ctx 0 params.length) :=
  Nat.zero_add params.length ▸ elabFrom TermContext.empty params

def VParams.elabFrom {n : Nat} (ctx : TermContext n) (params : List Ast) :
    OptionT ElabM (TermContext (n + params.length) × Tele VParam n (n + params.length)) :=
  Nat.zero_add params.length ▸ go n 0 ctx .nil params
  where
    go {a : Nat} (b : Nat) (idx : Nat) (ctx : TermContext b) (acc : Tele VParam a b) :
      (params : List Ast) →
      OptionT ElabM (TermContext (b + params.length) × Tele VParam a (b + params.length))
    | [] => return (ctx, acc)
    | ast :: bs => do
        let some (name, tyAst) := getTypedBinder ast
          | failure
        let ty ← OptionT.lift (withChild idx (withChild 1 (checkTy ctx tyAst)))
        let tyVal ← ty.eval ctx.env
        let tyQuoted ← tyVal.quote
        withChild idx (withChild 0 (emitHover (.localVar name ctx.names tyQuoted)))
        let ctx := ctx.bind name tyVal
        let ih ← go (b + 1) (idx + 1) ctx (acc.snoc ⟨name, tyVal⟩) bs
        return by simpa only [List.length_cons, Nat.add_comm bs.length, Nat.add_assoc b] using ih

def VParams.elab (params : List Ast) :
    OptionT ElabM (TermContext params.length × Tele VParam 0 params.length) := by
  simpa only [Nat.zero_add] using elabFrom TermContext.empty params

end Qdt
