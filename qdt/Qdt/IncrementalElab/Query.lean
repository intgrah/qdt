import Std.Data.HashMap
import Std.Data.HashSet

import Qdt.MLTT.Global
import Qdt.Frontend.Ast

namespace Qdt.Incremental

open Lean (Name)
open Std (HashMap HashSet)
open System (FilePath)

inductive TopKind : Type
  | definition
  | axiom
  | inductive
  | structure
  | example
deriving DecidableEq, Repr, Inhabited, Hashable

structure TopDecl where
  kind : TopKind
  name : Name
deriving DecidableEq, Repr, Inhabited, Hashable

abbrev GlobalEnv := HashMap Name Entry

inductive Key : Type
  | inputFiles
  | moduleFile (modName : Name)
  | moduleImports (file : FilePath)
  | elabModule (file : FilePath)

  | fileText (file : FilePath)
  | astProgram (file : FilePath)
  | declOwner (file : FilePath)
  | topDeclCmd (file : FilePath) (decl : TopDecl)
  | elabTop (file : FilePath) (decl : TopDecl)
  | entry (file : FilePath) (name : Name)
  | constTy (file : FilePath) (name : Name)
  | constantInfo (file : FilePath) (name : Name)
  | constDef (file : FilePath) (name : Name)
  | recursorInfo (file : FilePath) (name : Name)
  | constructorInfo (file : FilePath) (name : Name)
  | inductiveInfo (file : FilePath) (name : Name)
deriving DecidableEq, Repr, Inhabited, Hashable

def Val : Key → Type
  | .inputFiles => HashSet FilePath
  | .moduleFile _ => Option FilePath
  | .moduleImports _ => List Name
  | .elabModule _ => GlobalEnv

  | .fileText _ => String
  | .astProgram _ => Frontend.Ast.Program
  | .declOwner _ => HashMap Name TopDecl
  | .topDeclCmd _ _ => Frontend.Ast.Command.Cmd
  | .elabTop _ _ => HashMap Name Entry
  | .entry _ _ => Option Entry
  | .constTy _ _ => Option (Ty 0)
  | .constantInfo _ _ => Option ConstantInfo
  | .constDef _ _ => Option (Tm 0)
  | .recursorInfo _ _ => Option RecursorInfo
  | .constructorInfo _ _ => Option ConstructorInfo
  | .inductiveInfo _ _ => Option InductiveInfo

end Qdt.Incremental
