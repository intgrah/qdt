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
  ctx := Tele.nil
  env := Env.nil

def TermContext.bind {n} (name : Name) (ty : VTy n) (tctx : TermContext n) : TermContext (n + 1) where
  ctx := tctx.ctx.snoc ⟨name, ty⟩
  env := tctx.env.weaken.cons (VTm.varAt n)

def TermContext.define {n} (name : Name) (ty : VTy n) (value : VTm n) (tctx : TermContext n) : TermContext (n + 1) where
  ctx := tctx.ctx.snoc ⟨name, ty⟩
  env := tctx.env.weaken.cons value.weaken

def Tele.lookup {n} : Idx n → Tele VParam 0 n → VTy n
  | ⟨0, _⟩, .snoc _ ⟨_, ty⟩ => ty.weaken
  | ⟨i + 1, _⟩, .snoc ctx' _ => (lookup ⟨i, by omega⟩ ctx').weaken

def TermContext.lookup {n} (i : Idx n) (tctx : TermContext n) : VTy n :=
  tctx.ctx.lookup i

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

def Tele.names {n} : Tele VParam 0 n → List Name
  | .nil => []
  | .snoc ts ⟨name, _⟩ => name :: ts.names

def TermContext.names {n} (tctx : TermContext n) : List Name :=
  tctx.ctx.names

end Qdt
