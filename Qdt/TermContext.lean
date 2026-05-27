module

public import Qdt.Semantics

@[expose] public section

namespace Qdt

open Lean (Name)

structure VEntry (n : Nat) where
  name : Name
  ty : VTy n
  value? : Option (VTm n) := none

abbrev VEntry.bound {n} (name : Name) (ty : VTy n) : VEntry n :=
  { name, ty, value? := none }

abbrev VEntry.defined {n} (name : Name) (ty : VTy n) (value : VTm n) : VEntry n :=
  { name, ty, value? := some value }

def VCtx : Nat → Type := Tele VEntry 0

structure TermContext (n : Nat) where
  ctx : VCtx n
  env : Env n n -- Pre-weakened environment

def TermContext.empty : TermContext 0 where
  ctx := Tele.nil
  env := Env.nil

def TermContext.bind {n} (name : Name) (ty : VTy n) (tctx : TermContext n) : TermContext (n + 1) where
  ctx := tctx.ctx.snoc (.bound name ty)
  env := tctx.env.weaken.cons (VTm.varAt n)

def TermContext.define {n} (name : Name) (ty : VTy n) (value : VTm n) (tctx : TermContext n) : TermContext (n + 1) where
  ctx := tctx.ctx.snoc (.defined name ty value)
  env := tctx.env.weaken.cons value.weaken

def VCtx.lookupNameTy {n} : Idx n → VCtx n → Name × VTy n
  | ⟨0, _⟩, .snoc _ entry => (entry.name, entry.ty.weaken)
  | ⟨i + 1, _⟩, .snoc ctx' _ =>
      let (name, ty) := lookupNameTy ⟨i, by omega⟩ ctx'
      (name, ty.weaken)

@[inline] def VCtx.lookup {n} (i : Idx n) (ctx : VCtx n) : VTy n :=
  (ctx.lookupNameTy i).snd

@[inline] def VCtx.lookupByLevel {n} (lvl : Lvl n) (ctx : VCtx n) : Name × VTy n :=
  ctx.lookupNameTy lvl.rev

def TermContext.lookup {n} (i : Idx n) (tctx : TermContext n) : VTy n :=
  tctx.ctx.lookup i

def TermContext.findName? {n} (name : Name) (tctx : TermContext n) : Option (Idx n × VTy n) :=
  let rec go {n} : Tele VEntry 0 n → Option (Idx n × VTy n)
    | .nil => none
    | .snoc ts entry => do
      if entry.name = name then
        return (⟨0, by omega⟩, entry.ty.weaken)
      else
        let (k, ty) ← go ts
        return (k.succ, ty.weaken)
  go tctx.ctx

def VCtx.names {n} : VCtx n → List Name
  | .nil => []
  | .snoc ts entry => entry.name :: VCtx.names ts

def TermContext.names {n} (tctx : TermContext n) : List Name :=
  tctx.ctx.names

end Qdt
