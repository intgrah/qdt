import Std.Data.TreeMap

import Qdt.MLTT.Syntax
import Qdt.Semantics
import Qdt.Tele

namespace Qdt

open Lean (Name)

structure TermContext (n : Nat) where
  ctx : Tele VParam 0 n
  env : Env n n -- Pre-weakened environment

def TermContext.empty : TermContext 0 where
  ctx := .nil
  env := .nil

def TermContext.bind {n} (name : Name) (ty : VTy n) (tctx : TermContext n) : TermContext (n + 1) where
  ctx := tctx.ctx.snoc ⟨name, ty⟩
  env := tctx.env.weaken.cons (VTm.varAt n)

def TermContext.define {n} (name : Name) (ty : VTy n) (value : VTm n) (tctx : TermContext n) : TermContext (n + 1) where
  ctx := tctx.ctx.snoc ⟨name, ty⟩
  env := tctx.env.weaken.cons value.weaken

def TermContext.findName? {n} (name : Name) (tctx : TermContext n) : Option (Idx n × VTy n) :=
  let rec go {n} : Tele VParam 0 n → Option (Idx n × VTy n)
    | .nil => none
    | .snoc ts ⟨n, ty⟩ => do
      if n = name then
        return (⟨0, by omega⟩, ty.weaken)
      else
        let (k, ty) ← go ts
        return (k.succ, ty.weaken)
  go tctx.ctx

def TermContext.names {n} (tctx : TermContext n) : List Name :=
  let rec go {n} : Tele VParam 0 n → List Name
    | .nil => []
    | .snoc ts ⟨name, _⟩ => name :: go ts
  go tctx.ctx

end Qdt
