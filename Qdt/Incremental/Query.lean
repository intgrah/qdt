module

public import Qdt.Error
public import Qdt.Semantics
public import Qdt.Theory.Global
public import Incremental.Basic


@[expose] public section

namespace Qdt

open Lean (Name)
open Std (HashMap HashSet)
open System (FilePath)
open Frontend (Ast SourceMap)
open Frontend.Parser (ParseError)

inductive InputKey : Type
  | text (filepath : FilePath)
  | inputFiles
deriving DecidableEq, Repr, Inhabited, Hashable

abbrev InputVal : InputKey → Type
  | .text _ => String
  | .inputFiles => HashSet FilePath

abbrev InputV := Option ∘ InputVal

inductive Key : Type
  | astSourceMap (filepath : FilePath)
  | ast (filepath : FilePath)
  | sourceMap (filepath : FilePath)
  | imports (filePath : FilePath)
  | declarationIndex (filePath : FilePath)
  | declScope (filepath : FilePath) (name : Name) (currentDecl : Name)
  | declAst (filepath : FilePath) (name : Name)
  | elabOwner (filepath : FilePath) (owner : Name)
  | elabDecl (filepath : FilePath) (name : Name)
  | lookup (filepath : FilePath) (name : Name)
  | lookupInfo (filepath : FilePath) (name : Name)
  | constant (filepath : FilePath) (name : Name)
  | transitiveImports (filepath : FilePath)
  | type (filepath : FilePath) (name : Name)
  | moduleFile (modName : Name)
  | eval (filepath : FilePath) (name : Name) (univs : List Universe)
  | checkFile (filepath : FilePath)
  | checkProject
deriving DecidableEq, Repr, Inhabited, Hashable

def Key.tag : Key → String
  | .astSourceMap _ => "astSourceMap"
  | .ast _ => "ast"
  | .sourceMap _ => "sourceMap"
  | .imports _ => "imports"
  | .declarationIndex _ => "declarationIndex"
  | .declScope _ _ _ => "declScope"
  | .declAst _ _ => "declAst"
  | .elabOwner _ _ => "elabOwner"
  | .elabDecl _ _ => "elabDecl"
  | .lookup _ _ => "lookup"
  | .lookupInfo _ _ => "lookupInfo"
  | .constant _ _ => "constant"
  | .transitiveImports _ => "transitiveImports"
  | .type _ _ => "type"
  | .eval _ _ _ => "eval"
  | .moduleFile _ => "moduleFile"
  | .checkFile _ => "checkFile"
  | .checkProject => "checkProject"

def Key.display : Key → String
  | .astSourceMap p => s!"astSourceMap:{p}"
  | .ast p => s!"ast:{p}"
  | .sourceMap p => s!"sourceMap:{p}"
  | .imports p => s!"imports:{p}"
  | .declarationIndex p => s!"declarationIndex:{p}"
  | .declScope p n cd => s!"declScope:{p}:{n}<{cd}"
  | .declAst p n => s!"declAst:{p}:{n}"
  | .elabOwner p n => s!"elabOwner:{p}:{n}"
  | .elabDecl p n => s!"elabDecl:{p}:{n}"
  | .lookup p n => s!"lookup:{p}:{n}"
  | .lookupInfo p n => s!"lookupInfo:{p}:{n}"
  | .constant p n => s!"constant:{p}:{n}"
  | .transitiveImports p => s!"transitiveImports:{p}"
  | .type p n => s!"type:{p}:{n}"
  | .eval p n us => s!"eval:{p}:{n}:{us}"
  | .moduleFile m => s!"moduleFile:{m}"
  | .checkFile p => s!"checkFile:{p}"
  | .checkProject => "checkProject"

def InputKey.display : InputKey → String
  | .text p => s!"text:{p}"
  | .inputFiles => "inputFiles"

abbrev Val : Key → Type
  | .astSourceMap _ => Ast × SourceMap × Array Diagnostic
  | .ast _ => Ast
  | .sourceMap _ => SourceMap
  | .imports _ => Array Name
  | .declarationIndex _ => HashMap Name Nat × Array Diagnostic
  | .declScope _ _ _ => Bool
  | .declAst _ _ => Option Ast
  | .elabOwner _ _ => Std.HashMap Name Constant × ElabInfo
  | .elabDecl _ _ => Option Constant × ElabInfo
  | .lookup _ _ => Option Constant
  | .lookupInfo _ _ => ElabInfo
  | .constant _ _ => Option Constant
  | .transitiveImports _ => HashSet FilePath
  | .type _ _ => Option ConstantInfo
  | .eval _ _ _ => Option (VTm 0)
  | .moduleFile _ => Option FilePath
  | .checkFile _ => Array Diagnostic
  | .checkProject => Array Diagnostic

instance {α} [Hashable α] : Hashable (HashMap Name α) where
  hash m := hash <| m.toArray

instance {α} [BEq α] [Hashable α] : Hashable (HashSet α) where
  hash m := hash <| m.toArray

instance {q} : Hashable (Val q) := by
  cases q <;> infer_instance

instance {q} : Inhabited (Val q) := by
  cases q <;> infer_instance

instance {i} : Hashable (InputVal i) := by
  cases i <;> infer_instance

instance {i} : Hashable (InputV i) :=
  inferInstanceAs (Hashable (Option (InputVal i)))

def Key.rank : Key → Nat
  | .moduleFile _ => 0
  | .astSourceMap _ => 1
  | .ast _ => 2
  | .sourceMap _ => 2
  | .imports _ => 4
  | .declarationIndex _ => 4
  | .transitiveImports _ => 5
  | .declAst _ _ => 5
  | .declScope _ _ _ => 6
  | .elabOwner _ _ => 6
  | .elabDecl _ _ => 7
  | .lookup _ _ => 8
  | .lookupInfo _ _ => 8
  | .constant _ _ => 9
  | .type _ _ => 10
  | .eval _ _ _ => 10
  | .checkFile _ => 11
  | .checkProject => 12

abbrev config : Incremental.BuildConfig where
  I := InputKey
  V := InputV
  Q := Key
  R := Val
  rel q q₀ := q.rank < q₀.rank
  wf := InvImage.wf Key.rank Nat.lt_wfRel.wf

end Qdt
