import Std.Data.HashMap
import Std.Data.HashSet

import Qdt.Error
import Qdt.MLTT.Global
import Qdt.Frontend.Ast
import Qdt.Incremental.Basic

namespace Qdt

namespace Incremental

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

abbrev fetchQ := TaskM.fetch (ε := Error) (Q := Key) (R := Val)

end Incremental

export Incremental (fetchQ)

end Qdt
