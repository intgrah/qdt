import Std.Data.HashMap
import Std.Data.HashSet

import Qdt.Error
import Qdt.MLTT.Global
import Qdt.Frontend.Ast
import Qdt.Frontend.Cst
import Qdt.Incremental.Basic

namespace Qdt

namespace Incremental

open Lean (Name)
open Std (HashMap HashSet)
open System (FilePath)

inductive Key : Type
  | inputFiles
  | moduleFile (modName : Name)
  | moduleImports (filepath : FilePath)
  | importedEnv (filepath : FilePath)
  | fileText (filepath : FilePath)
  | astProgram (filepath : FilePath)
  | sourceMap (filepath : FilePath)
  | declOwner (filepath : FilePath)
  | elabCmd (filepath : FilePath) (declName : Name)
  | elabModule (filepath : FilePath)
  | entry (filepath : FilePath) (name : Name)
deriving DecidableEq, Repr, Inhabited, Hashable

def Val : Key → Type
  | .inputFiles => HashSet FilePath
  | .moduleFile .. => Option FilePath
  | .moduleImports .. => List Name
  | .importedEnv .. => Global
  | .fileText .. => String
  | .astProgram .. => Array Frontend.Ast
  | .sourceMap .. => Frontend.SourceMap
  | .declOwner .. => HashMap Name Name
  | .elabCmd .. => HashMap Name Entry × ElabInfo
  | .elabModule .. => Global × ElabInfo
  | .entry .. => Option Entry

abbrev fetchQ := TaskM.fetch (Q := Key) (R := Val)

end Incremental

export Incremental (fetchQ)

end Qdt
