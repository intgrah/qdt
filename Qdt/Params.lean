import Qdt.Bidirectional
import Qdt.Control
import Qdt.Frontend.Ast

namespace Qdt

open Lean (Name)
open Frontend (Ast)

private def getTypedBinder (ast : Ast) : Option (Name × Ast) :=
  match ast with
  | .node `Binder.typed #[.ident name, ty] => some (name, ty)
  | _ => none

/-- Elaborate parameters and return their types with universe levels -/
def elabParamsWithLevels {n} (params : List Ast) :
    TermM n (TermContext (n + params.length) × Ctx n (n + params.length) × List Universe) :=
  Nat.zero_add params.length ▸  go n 0 .nil [] params
  where
    go {a : Nat} (b : Nat) (idx : Nat) (acc : Ctx a b) (levels : List Universe) :
      (params : List Ast) →
        TermM b (TermContext (b + params.length) × Ctx a (b + params.length) × List Universe)
    | [] => return (← read, acc, levels.reverse)
    | p :: bs => do
        let some (name, tyAst) := getTypedBinder p
          | throw (.syntaxError)
        let (ty, level) ← withChildTm idx (withChildTm 1 (checkTyWithLevel tyAst))
        let ctx ← read
        let tyVal ← ty.eval ctx.env
        withChildTm idx (withChildTm 0 (emitType tyVal))
        let ctx := ctx.bind name tyVal
        let ih ← go (b + 1) (idx + 1) (acc.snoc ⟨name, ty⟩) (level :: levels) bs ctx
        return by simpa only [List.length_cons, Nat.add_comm bs.length, Nat.add_assoc b] using ih

def elabParamsFrom {n} (params : List Ast) :
    TermM n (TermContext (n + params.length) × Ctx n (n + params.length)) := do
  let (ctx, tele, _) ← elabParamsWithLevels params
  return (ctx, tele)


def elabParams (params : List Ast) :
    MetaM (TermContext params.length × Ctx 0 params.length) :=
  Nat.zero_add params.length ▸ elabParamsFrom params TermContext.empty

def elabVParamsFrom {n} (params : List Ast) :
    TermM n (TermContext (n + params.length) × Tele VParam n (n + params.length)) :=
  Nat.zero_add params.length ▸ go n 0 .nil params
  where
    go {a : Nat} (b : Nat) (idx : Nat) (acc : Tele VParam a b) :
      (params : List Ast) →
      TermM b (TermContext (b + params.length) × Tele VParam a (b + params.length))
    | [] => return (← read, acc)
    | p :: bs => do
        let some (name, tyAst) := getTypedBinder p
          | throw (.syntaxError)
        let ty ← withChildTm idx (withChildTm 1 (checkTy tyAst))
        let ctx ← read
        let tyVal ← ty.eval ctx.env
        withChildTm idx (withChildTm 0 (emitType tyVal))
        let ctx := ctx.bind name tyVal
        let ih ← go (b + 1) (idx + 1) (acc.snoc ⟨name, tyVal⟩) bs ctx
        return by simpa only [List.length_cons, Nat.add_comm bs.length, Nat.add_assoc b] using ih


def elabVParams (params : List Ast) :
    MetaM (TermContext params.length × Tele VParam 0 params.length) := by
  simpa only [Nat.zero_add] using elabVParamsFrom params TermContext.empty

end Qdt
