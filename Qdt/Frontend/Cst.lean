module

public import Qdt.Frontend.Ast
public import Std.Data.HashMap.Basic

@[expose] public section

namespace Qdt.Frontend

open Lean (Name Syntax SyntaxNodeKind)
open Std (HashMap)

inductive Cst : Type
  | token (kind : SyntaxNodeKind) (val : String)
  | node (kind : SyntaxNodeKind) (children : Array Cst)
with
  @[computed_field]
  width : Cst → Nat
    | .token _ val => val.length
    | .node _ children => children.map width |>.sum
deriving Hashable, Inhabited

structure Span where
  startPos : Nat
  endPos : Nat

namespace Cst

def reconstruct : Cst → String
  | .token _ val => val
  | .node _ children => children.foldl (fun acc c => acc ++ c.reconstruct) ""

def spanAtPath (root : Cst) (path : Path) : Option Span := do
  let mut current := root
  let mut startPos := 0
  for idx in path do
    match current with
    | .node _ children =>
        for h : i in [:idx] do
          if hi : i < children.size then
            startPos := startPos + children[i].width
        if hj : idx < children.size then
          current := children[idx]
        else
          failure
    | .token _ _ => failure
  return { startPos, endPos := startPos + current.width }

def pathAtPosition (root : Cst) (pos : Nat) : Path :=
  go root pos []
where
  go (cst : Cst) (pos : Nat) (acc : Path) : Path :=
    match cst with
    | .token _ _ => acc.reverse
    | .node _ children => Id.run do
        let mut offset := 0
        for h : i in [:children.size] do
          let child := children[i]
          let childWidth := child.width
          if offset ≤ pos ∧ pos < offset + childWidth then
            return go child (pos - offset) (i :: acc)
          offset := offset + childWidth
        return acc.reverse

def ofLeanSyntax : Syntax → Cst
  | .missing => .token `missing ""
  | .atom _ val => .token `atom val
  | .ident _ rawVal _ _ => .token `ident rawVal.toString
  | .node _ kind args => Cst.node kind (args.map ofLeanSyntax)

end Cst

structure SourceMap where
  astToSpan : HashMap Path Span
deriving Inhabited

instance : Hashable SourceMap where
  hash sm := hash sm.astToSpan.size

namespace SourceMap

def empty (cap : Nat := 16) : SourceMap where
  astToSpan := HashMap.emptyWithCapacity cap

def insert (m : SourceMap) (astPath : Path) (span : Span) : SourceMap where
  astToSpan := m.astToSpan.insert astPath span

def spanForAstPath (m : SourceMap) (path : Path) : Option Span :=
  m.astToSpan[path]?

def astPathAtPosition (m : SourceMap) (pos : Nat) : Option Path := Id.run do
  let mut best : Option Path := none
  for (path, span) in m.astToSpan do
    if span.startPos ≤ pos ∧ pos < span.endPos then
      match best with
      | none => best := some path
      | some prev =>
          if path.length > prev.length then
            best := some path
  return best

def resolveSpan (m : SourceMap) (path : Path) : Option Span := Id.run do
  let fwd := path.reverse
  for len in (List.range fwd.length).reverse do
    let pre := fwd.take (len + 1)
    if let some span := m.astToSpan[pre]? then
      return some span
  return none

end SourceMap

end Qdt.Frontend
