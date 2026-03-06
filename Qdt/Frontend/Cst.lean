import Qdt.Frontend.Ast
import Std.Data.HashMap

namespace Qdt.Frontend

open Lean (Name Syntax SyntaxNodeKind)
open Std (HashMap)

inductive Cst : Type
  | token (kind : SyntaxNodeKind) (val : String)
  | node (kind : SyntaxNodeKind) (children : Array Cst)
deriving Hashable

structure Span where
  startPos : Nat
  endPos : Nat

namespace Cst

def width : Cst → Nat
  | .token _ val => val.length
  | .node _ children => children.foldl (· + ·.width) 0

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
  cstToAst : HashMap Path Path
  astToCst : HashMap Path Path

instance : Hashable SourceMap where
  hash sm := mixHash (hash sm.cstToAst.size) (hash sm.astToCst.size)

namespace SourceMap

def insert (m : SourceMap) (cstPath : Path) (astPath : Path) : SourceMap where
  cstToAst := m.cstToAst.insert cstPath astPath
  astToCst := m.astToCst.insert astPath cstPath

end SourceMap

end Qdt.Frontend
