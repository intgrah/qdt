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
open Frontend (Ast Cst SourceMap)
open Frontend.Parser (ParseError)

structure Origin where
  filepath : FilePath
  idx : Nat
deriving DecidableEq, Repr, Hashable, Inhabited

inductive InputKey : Type
  | text (filepath : FilePath)
  | inputFiles
deriving DecidableEq, Repr, Inhabited, Hashable

abbrev InputVal : InputKey → Type
  | .text _ => String
  | .inputFiles => HashSet FilePath

abbrev InputV := Option ∘ InputVal

inductive Key : Type
  | cst (filepath : FilePath)
  | astSourceMap (filepath : FilePath)
  | ast (filepath : FilePath)
  | sourceMap (filepath : FilePath)
  | imports (filePath : FilePath)
  | declarationIndex (filePath : FilePath)
  | declAst (filepath : FilePath) (name : Name)
  | elabCmdAt (filepath : FilePath) (idx : Nat)
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
  | .cst _ => "cst"
  | .astSourceMap _ => "astSourceMap"
  | .ast _ => "ast"
  | .sourceMap _ => "sourceMap"
  | .imports _ => "imports"
  | .declarationIndex _ => "declarationIndex"
  | .declAst _ _ => "declAst"
  | .elabCmdAt _ _ => "elabCmdAt"
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
  | .cst p => s!"cst:{p}"
  | .astSourceMap p => s!"astSourceMap:{p}"
  | .ast p => s!"ast:{p}"
  | .sourceMap p => s!"sourceMap:{p}"
  | .imports p => s!"imports:{p}"
  | .declarationIndex p => s!"declarationIndex:{p}"
  | .declAst p n => s!"declAst:{p}:{n}"
  | .elabCmdAt p i => s!"elabCmdAt:{p}:{i}"
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
  | .cst _ => Cst × Array ParseError
  | .astSourceMap _ => Ast × SourceMap × Array Diagnostic
  | .ast _ => Ast
  | .sourceMap _ => SourceMap
  | .imports _ => Array Name
  | .declarationIndex _ => HashMap Name Nat × Array Diagnostic
  | .declAst _ _ => Option (Ast × Nat)
  | .elabCmdAt _ _ => Global × ElabInfo
  | .elabDecl _ _ => Option (Constant × Origin) × ElabInfo
  | .lookup _ _ => Option (Constant × Origin)
  | .lookupInfo _ _ => ElabInfo
  | .constant _ _ => Option (Constant × Origin)
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

abbrev config : Incremental.BuildConfig where
  I := InputKey
  V := InputV
  Q := Key
  R := Val
  rel := sorry
  wf := sorry

end Qdt
