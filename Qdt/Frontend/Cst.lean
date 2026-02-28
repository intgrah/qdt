import Qdt.Frontend.Ast
import Std.Data.HashMap

namespace Qdt.Frontend

open Lean (Name Syntax SyntaxNodeKind)
open Std (HashMap)

inductive Cst : Type
  | token (kind : SyntaxNodeKind) (val : String)
  | node (kind : SyntaxNodeKind) (children : Array Cst)
deriving Repr, Inhabited

structure Span where
  startPos : Nat
  endPos : Nat
deriving Repr, Inhabited

namespace Cst

def width : Cst → Nat
  | .token _ val => val.length
  | .node _ children => children.foldl (· + ·.width) 0

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

partial def pathAtPosition (root : Cst) (pos : Nat) : Path :=
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

abbrev CstPath := Path
abbrev AstPath := Path

structure SourceMap where
  cstToAst : HashMap CstPath AstPath
  astToCst : HashMap AstPath CstPath

instance : Hashable SourceMap where
  hash sm := mixHash (hash sm.cstToAst.size) (hash sm.astToCst.size)

namespace SourceMap

def insert (m : SourceMap) (cstPath : CstPath) (astPath : AstPath) : SourceMap where
  cstToAst := m.cstToAst.insert cstPath astPath
  astToCst := m.astToCst.insert astPath cstPath

end SourceMap

end Qdt.Frontend
