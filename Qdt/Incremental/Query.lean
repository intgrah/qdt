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

inductive Key : Type
  | inputFiles
  | moduleFile (modName : Name)
  | moduleImports (filepath : FilePath)
  | importedEnv (filepath : FilePath)
  | elabModule (filepath : FilePath)
    /-- String content of a file -/
  | fileText (filepath : FilePath)
    /-- AST of a file -/
  | astProgram (filepath : FilePath)
  | declOwner (filepath : FilePath)
  | declOrdering (filepath : FilePath)
  | topDeclCmd (filepath : FilePath) (decl : TopDecl)
  | elabTop (filepath : FilePath) (decl : TopDecl)
  | entry (filepath : FilePath) (name : Name)
    /-- Type of any global entry -/
  | constTy (filepath : FilePath) (name : Name)
  | constantInfo (filepath : FilePath) (name : Name)
    /-- Definition of a def entry -/
  | constDef (filepath : FilePath) (name : Name)
  | recursorInfo (filepath : FilePath) (name : Name)
  | constructorInfo (filepath : FilePath) (name : Name)
  | inductiveInfo (filepath : FilePath) (name : Name)
deriving DecidableEq, Repr, Inhabited, Hashable

def Val : Key → Type
  | .inputFiles => HashSet FilePath
  | .moduleFile .. => Option FilePath
  | .moduleImports .. => List Name
  | .importedEnv .. => Global
  | .elabModule .. => Global

  | .fileText .. => String
  | .astProgram .. => Frontend.Ast.Program
  | .declOwner .. => HashMap Name TopDecl
  | .declOrdering .. => List TopDecl
  | .topDeclCmd .. => Frontend.Ast.Command.Cmd
  | .elabTop .. => HashMap Name Entry
  | .entry .. => Option Entry
  | .constTy .. => Option (Ty 0)
  | .constantInfo .. => Option ConstantInfo
  | .constDef .. => Option (Tm 0)
  | .recursorInfo .. => Option RecursorInfo
  | .constructorInfo .. => Option ConstructorInfo
  | .inductiveInfo .. => Option InductiveInfo

end Qdt.Incremental
