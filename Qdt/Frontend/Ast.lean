import Lean.Data.Name

namespace Qdt.Frontend

open Lean (Name SyntaxNodeKind)

abbrev Path := List Nat

inductive Ast : Type
  | node (kind : SyntaxNodeKind) (children : Array Ast)
  | ident (name : Name)
  | missing
deriving Repr, Inhabited, Hashable, BEq

namespace Ast

def kind? : Ast → Option SyntaxNodeKind
  | .node k _ => some k
  | _ => none

def children? : Ast → Option (Array Ast)
  | .node _ cs => some cs
  | _ => none

def name? : Ast → Option Name
  | .ident n => some n
  | _ => none

def child? (ast : Ast) (i : Nat) : Option Ast :=
  match ast with
  | .node _ cs => cs[i]?
  | _ => none

@[inline] def getName : Ast → Name
  | .ident n => n
  | _ => .anonymous

end Ast

end Qdt.Frontend
