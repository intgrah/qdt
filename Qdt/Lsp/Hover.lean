import Qdt.MLTT.Global
import Qdt.MLTT.Syntax
import Qdt.Pretty
import Qdt.Frontend.Source
import Qdt.TypeOf
import Qdt.Quote
import Qdt.Control

namespace Qdt.Frontend

def Span.contains (span : Span) (pos : String.Pos.Raw) : Bool :=
  span.startPos.byteIdx ≤ pos.byteIdx ∧ pos.byteIdx < span.endPos.byteIdx

def Src.contains (src : Src) (pos : String.Pos.Raw) : Bool :=
  match src with
  | none => false
  | some span => span.contains pos

end Qdt.Frontend

namespace Qdt.Lsp

open Lean (Name Format ToFormat format)

structure HoverResult where
  contents : String
  span : Frontend.Span
deriving Repr

structure LocalVar where
  name : Name
  tyStr : String
deriving Repr

structure WalkCtx (n : Nat) where
  locals : List LocalVar
  names : List Name
  tctx : TermContext n

def WalkCtx.empty : WalkCtx 0 where
  locals := []
  names := []
  tctx := .empty

def WalkCtx.extend {n} (ctx : WalkCtx n) (name : Name) (ty : Ty n) (tyVal : VTy n) : WalkCtx (n + 1) where
  locals := ⟨name, Format.pretty (Ty.fmt ctx.names ty Prec.min)⟩ :: ctx.locals
  names := name :: ctx.names
  tctx := ctx.tctx.bind name tyVal

def WalkCtx.lookupVar {n} (ctx : WalkCtx n) (i : Nat) : Option LocalVar :=
  ctx.locals[i]?

def WalkCtx.lookupConstTy (name : Name) : MetaM (Option (Ty 0)) := do
  let info? ← fetchConstantInfo name
  return info?.map (·.ty)

def WalkCtx.fmtTy {n m} (ctx : WalkCtx n) (ty : Ty m) : String :=
  Format.pretty (Ty.fmt ctx.names ty Prec.min)

def WalkCtx.fmtTm {n m} (ctx : WalkCtx n) (tm : Tm m) : String :=
  Format.pretty (Tm.fmt ctx.names tm Prec.min)

def WalkCtx.inferType {n} (ctx : WalkCtx n) (tm : Tm n) : MetaM String := do
  try
    let vty ← Tm.typeOf tm ctx.tctx
    let ty ← vty.quote
    return ctx.fmtTy ty
  catch _ => return "?"

def WalkCtx.evalTy {n} (ctx : WalkCtx n) (ty : Ty n) : MetaM (VTy n) := do
  try
    ty.eval ctx.tctx.env
  catch _ => return .u .zero

def WalkCtx.evalTmTy {n} (ctx : WalkCtx n) (tm : Tm n) : MetaM (VTy n) := do
  try
    let vtm ← tm.eval ctx.tctx.env
    doEl vtm
  catch _ => return .u .zero

def WalkCtx.inferTyLevel {n} (ctx : WalkCtx n) (ty : Ty n) : MetaM String := do
  try
    let vty ← ty.eval ctx.tctx.env
    let level ← vty.inferLevel ctx.tctx.ctx
    return s!"Type {level}"
  catch _ => return "Type"

mutual

partial def findInTy {n} (ctx : WalkCtx n) (pos : String.Pos.Raw) : Ty n → MetaM (Option HoverResult)
  | .u src level =>
      if src.contains pos then
        return src.bind fun span => some { contents := s!"Type {Universe.succ level}", span }
      else return none
  | .pi src ⟨paramSrc, name, dom⟩ cod => do
      if let some r ← findInTy ctx pos dom then return some r
      let domVal ← ctx.evalTy dom
      let ctx' := ctx.extend name dom domVal
      if let some r ← findInTy ctx' pos cod then return some r
      if !name.isAnonymous && paramSrc.contains pos then
        return paramSrc.bind fun span => some { contents := s!"{name} : {ctx.fmtTy dom}", span }
      if src.contains pos then
        let tyStr ← ctx.inferTyLevel (.pi src ⟨paramSrc, name, dom⟩ cod)
        return src.bind fun span => some { contents := tyStr, span }
      return none
  | .el _ t => findInTm ctx pos t

partial def findInTm {n} (ctx : WalkCtx n) (pos : String.Pos.Raw) : Tm n → MetaM (Option HoverResult)
  | .u' src level =>
      if src.contains pos then
        return src.bind fun span => some { contents := s!"Type {Universe.succ level}", span }
      else return none
  | .var src ⟨i, _⟩ =>
      if src.contains pos then
        return src.bind fun span =>
          match ctx.lookupVar i with
          | some ⟨name, tyStr⟩ => some { contents := s!"{name} : {tyStr}", span }
          | none => some { contents := s!"?{i}", span }
      else return none
  | .const src name us => do
      if src.contains pos then
        let nameWithUs :=
          if us.isEmpty then toString name
          else
            let usStrs := us.map (fun u => toString (Universe.reprPrec u 0))
            toString name ++ ".{" ++ ", ".intercalate usStrs ++ "}"
        let ty? ← WalkCtx.lookupConstTy name
        return src.bind fun span =>
          match ty? with
          | some ty => some { contents := s!"{nameWithUs} : {ctx.fmtTy ty}", span }
          | none => some { contents := nameWithUs, span }
      else return none
  | tm@(.lam src ⟨paramSrc, name, dom⟩ body) => do
      if let some r ← findInTy ctx pos dom then return some r
      let domVal ← ctx.evalTy dom
      let ctx' := ctx.extend name dom domVal
      if let some r ← findInTm ctx' pos body then return some r
      if !name.isAnonymous && paramSrc.contains pos then
        return paramSrc.bind fun span => some { contents := s!"{name} : {ctx.fmtTy dom}", span }
      if src.contains pos then
        let tyStr ← ctx.inferType tm
        return src.bind fun span => some { contents := tyStr, span }
      return none
  | tm@(.app src f a) => do
      if let some r ← findInTm ctx pos f then return some r
      if let some r ← findInTm ctx pos a then return some r
      if src.contains pos then
        let tyStr ← ctx.inferType tm
        return src.bind fun span => some { contents := tyStr, span }
      return none
  | tm@(.pi' src paramSrc name dom cod) => do
      if let some r ← findInTm ctx pos dom then return some r
      let domVal ← ctx.evalTmTy dom
      let ctx' := ctx.extend name (.el none dom) domVal
      if let some r ← findInTm ctx' pos cod then return some r
      if !name.isAnonymous && paramSrc.contains pos then
        return paramSrc.bind fun span => some { contents := s!"{name} : {ctx.fmtTm dom}", span }
      if src.contains pos then
        let tyStr ← ctx.inferType tm
        return src.bind fun span => some { contents := tyStr, span }
      return none
  | tm@(.proj src _ t) => do
      if let some r ← findInTm ctx pos t then return some r
      if src.contains pos then
        let tyStr ← ctx.inferType tm
        return src.bind fun span => some { contents := tyStr, span }
      return none
  | tm@(.letE src name ty val body) => do
      if let some r ← findInTy ctx pos ty then return some r
      if let some r ← findInTm ctx pos val then return some r
      let tyVal ← ctx.evalTy ty
      let ctx' := ctx.extend name ty tyVal
      if let some r ← findInTm ctx' pos body then return some r
      if src.contains pos then
        let tyStr ← ctx.inferType tm
        return src.bind fun span => some { contents := tyStr, span }
      return none

end

def findInEntry (ctx : WalkCtx 0) (pos : String.Pos.Raw) : Entry → MetaM (Option HoverResult)
  | .definition info => do
      if let some r ← findInTy ctx pos info.ty then return some r
      findInTm ctx pos info.tm
  | .opaque info
  | .axiom info
  | .constructor info
  | .inductive info
  | .recursor info =>
      findInTy ctx pos info.toConstantInfo.ty

def spanSize (span : Frontend.Span) : Nat :=
  span.endPos.byteIdx - span.startPos.byteIdx

def findHoverInGlobal (file : String) (pos : String.Pos.Raw) (global : Global) : IO (Option (Name × HoverResult)) := do
  let action : MetaM (Option (Name × HoverResult)) := do
    let ctx := WalkCtx.empty
    let entries := global.toList
    let mut best : Option (Name × HoverResult) := none
    for (name, entry) in entries do
      if entry.file == some file then
        if let some result ← findInEntry ctx pos entry then
          match best with
          | none => best := some (name, result)
          | some (_, prevResult) =>
              if spanSize result.span < spanSize prevResult.span then
                best := some (name, result)
    return best
  let coreCtx : CoreContext := { file := none, selfNames := [] }
  let coreState : CoreState := { modules := {}, importedEnv := global, localEnv := {}, errors := #[] }
  let metaCtx : MetaContext := { currentDecl := .anonymous }
  let metaState : MetaState := { sorryId := 0, univParams := [] }
  let fetchQ : ∀ q, Incremental.BaseM Error Incremental.Val (Incremental.Val q) := fun _ => throw (.msg "Internal error")
  let runState : Incremental.RunState Error Incremental.Val := {
    engine := {
      recover _ := throw (.msg "Internal error"),
      fingerprint _ _ := 0,
      isInput _ := false
    }
    started := {}
    stack := []
    deps := {}
  }
  let baseAction : Incremental.BaseM Error Incremental.Val (Except Error _) := do
    try
      let inner : QueryM ((Option (Name × HoverResult) × MetaState) × CoreState) :=
        action metaCtx |>.run metaState |>.run coreCtx |>.run coreState
      return .ok (← inner.run fetchQ).fst.fst
    catch e => return .error e
  let eioAction := baseAction.run' runState
  let result ← eioAction.toIO fun e => IO.Error.userError (toString e)
  return match result with
  | .ok result => result
  | .error _ => none

end Qdt.Lsp
