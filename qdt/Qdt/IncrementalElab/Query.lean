import Std.Data.HashMap

import Qdt.MLTT.Global
import Qdt.Frontend.Ast

namespace Qdt.Incremental

open Lean (Name)
open Std (HashMap)
open System (FilePath)

inductive TopKind : Type
  | definition
  | axiom
  | inductive
  | structure
deriving DecidableEq, Repr, Inhabited, Hashable

structure TopDecl where
  kind : TopKind
  name : Name
deriving DecidableEq, Repr, Inhabited, Hashable

inductive Key : Type
  | fileText (file : FilePath)
  | astProgram (file : FilePath)
  | declOwner (file : FilePath)
  | topDeclCmd (file : FilePath) (decl : TopDecl)
  | elabTop (file : FilePath) (decl : TopDecl)
  | entry (file : FilePath) (name : Name)
  | constTy (file : FilePath) (name : Name)
  | constDef (file : FilePath) (name : Name)
  | recursorInfo (file : FilePath) (name : Name)
  | constructorInfo (file : FilePath) (name : Name)
  | inductiveInfo (file : FilePath) (name : Name)
deriving DecidableEq, Repr, Inhabited, Hashable

def Val : Key → Type
  | .fileText _ => String
  | .astProgram _ => Frontend.Ast.Program
  | .declOwner _ => HashMap Name TopDecl
  | .topDeclCmd _ _ => Frontend.Ast.Command.Cmd
  | .elabTop _ _ => HashMap Name Entry
  | .entry _ _ => Option Entry
  | .constTy _ _ => Option (Ty 0)
  | .constDef _ _ => Option (Tm 0)
  | .recursorInfo _ _ => Option RecursorInfo
  | .constructorInfo _ _ => Option ConstructorInfo
  | .inductiveInfo _ _ => Option InductiveInfo
end Qdt.Incremental
