import Qdt.Bidirectional
import Qdt.Control
import Qdt.Frontend.Ast

namespace Qdt

open Lean (Name)

def elabParamsFrom {n} (params : List Frontend.Ast.TypedBinder) :
    TermM n (TermContext (n + params.length) × Tele Param n (n + params.length)) := by
  simpa only [Nat.zero_add] using elabParamsFrom.go n .nil params
  where
    elabParamsFrom.go
      {a : Nat}
      (b : Nat)
      (acc : Tele Param a b) :
      (params : List Frontend.Ast.TypedBinder) →
      TermM b (TermContext (b + params.length) × Tele Param a (b + params.length))
    | [] => return (← read, acc)
    | ⟨_src, name, ty⟩ :: bs => do
        let ty ← checkTy ty
        let ctx ← read
        let tyVal ← ty.eval ctx.env
        let ctx := ctx.bind name tyVal
        return by
          simpa only [List.length_cons, Nat.add_comm bs.length, ← Nat.add_assoc b]
          using ← elabParamsFrom.go (b + 1) (acc.snoc ⟨name, ty⟩) bs ctx


def elabParams (params : List Frontend.Ast.TypedBinder) :
    MetaM (TermContext params.length × Tele Param 0 params.length) := by
  simpa only [Nat.zero_add] using elabParamsFrom params TermContext.empty

def elabVParamsFrom {n} (params : List Frontend.Ast.TypedBinder) :
    TermM n (TermContext (n + params.length) × Tele VParam n (n + params.length)) := by
  simpa only [Nat.zero_add] using elabVParamsFrom.go n .nil params
  where
    elabVParamsFrom.go
      {a : Nat}
      (b : Nat)
      (acc : Tele VParam a b) :
      (params : List Frontend.Ast.TypedBinder) →
      TermM b (TermContext (b + params.length) × Tele VParam a (b + params.length))
    | [] => return (← read, acc)
    | ⟨_src, name, ty⟩ :: bs => do
        let ty ← checkTy ty
        let ctx ← read
        let tyVal ← ty.eval ctx.env
        let ctx := ctx.bind name tyVal
        return by
          simpa only [List.length_cons, Nat.add_comm bs.length, ← Nat.add_assoc b]
          using ← elabVParamsFrom.go (b + 1) (acc.snoc ⟨name, tyVal⟩) bs ctx


def elabVParams (params : List Frontend.Ast.TypedBinder) :
    MetaM (TermContext params.length × Tele VParam 0 params.length) := by
  simpa only [Nat.zero_add] using elabVParamsFrom params TermContext.empty

end Qdt
