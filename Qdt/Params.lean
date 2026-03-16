module

public import Qdt.Bidirectional

public section

namespace Qdt

open Lean (Name)
open Frontend (Ast Path)

variable (ι₀ : ∀ i, InputV i) (q₀ : Key)

def getTypedBinder : Ast → Option (Name × Ast)
  | .node `Binder.typed cs => some (cs[0]!.getName, cs[1]!)
  | _ => none

public def Params.elabWithLevels {n : Nat} (ctx : TermContext n) (params : List Ast) :
    OptionT (ElabM ι₀ q₀) (TermContext (n + params.length) × Ctx n (n + params.length) × List Universe) :=
  Nat.zero_add params.length ▸ go n 0 ctx .nil [] params
  where
    go {a : Nat} (b : Nat) (idx : Nat) (ctx : TermContext b) (acc : Ctx a b) (levels : List Universe) :
      (params : List Ast) →
        OptionT (ElabM ι₀ q₀) (TermContext (b + params.length) × Ctx a (b + params.length) × List Universe)
    | [] => return (ctx, acc, levels.reverse)
    | ast :: bs => do
        let some (name, tyAst) := getTypedBinder ast
          | failure
        let (ty, level) ← OptionT.lift (withChild ι₀ q₀ idx (withChild ι₀ q₀ 1 (checkTyWithLevel ι₀ q₀ ctx tyAst)))
        let tyVal ← ty.eval ι₀ q₀ ctx.env
        let tyQuoted ← tyVal.quote ι₀ q₀
        withChild ι₀ q₀ idx (withChild ι₀ q₀ 0 (emitHover ι₀ q₀ (.localVar name ctx.names tyQuoted)))
        let ctx := ctx.bind name tyVal
        let ih ← go (b + 1) (idx + 1) ctx (acc.snoc ⟨name, ty⟩) (level :: levels) bs
        return by simpa only [List.length_cons, Nat.add_comm bs.length, Nat.add_assoc b] using ih

public def Params.elabFrom {n : Nat} (ctx : TermContext n) (params : List Ast) :
    OptionT (ElabM ι₀ q₀) (TermContext (n + params.length) × Ctx n (n + params.length)) := do
  let (ctx, tele, _) ← Params.elabWithLevels ι₀ q₀ ctx params
  return (ctx, tele)

public def Params.elab (params : List Ast) :
    OptionT (ElabM ι₀ q₀) (TermContext params.length × Ctx 0 params.length) :=
  Nat.zero_add params.length ▸ Params.elabFrom ι₀ q₀ TermContext.empty params

end Qdt
