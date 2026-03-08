module

public import Qdt.Error
public import Qdt.Theory.Global

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

inductive Key : Type
  /-- Raw text of a file -/
  | text (filepath : FilePath)
  /-- Concrete syntax tree of a file -/
  | cst (filepath : FilePath)
  /-- Abstract syntax tree and source map of a file -/
  | astSourceMap (filepath : FilePath)
  /-- Abstract syntax tree of a file -/
  | ast (filepath : FilePath)
  /-- Source map produced when going from CST to AST -/
  | sourceMap (filepath : FilePath)
  /-- Modules imported from a file -/
  | imports (filePath : FilePath)
  /-- Map from a declaration to its index within a file -/
  | declarationIndex (filePath : FilePath)
  /--
  Fetch the specific AST node for a declaration.
  This allows granularity: if the file changes but this node doesn't,
  elaboration of this node is skipped.
  Returns the AST and its index in the file.
  -/
  | declAst (filepath : FilePath) (name : Name)
  /--
  Elaborate the command at a given index in a file.
  Shared key: all generated names from the same command use this.
  -/
  | elabCmdAt (filepath : FilePath) (idx : Nat)
  /--
  Elaborate a specific declaration.
  Returns the full elaboration result (Constant + Info).
  Delegates to `elabCmdAt`.
  -/
  | elabDecl (filepath : FilePath) (name : Name)
  /--
  Look up a declaration within a specific file.
  This is a projection of `elabDecl` that returns only Semantic info.
  If ElabInfo changes (e.g. whitespace/comments), this query remains unchanged.
  -/
  | lookup (filepath : FilePath) (name : Name)
  /--
  Look up elaboration info for a declaration.
  This is a projection of `elabDecl`.
  -/
  | lookupInfo (filepath : FilePath) (name : Name)
  /--
  Fetch a declaration from the project context (checking imports).
  The `filepath` refers to the file *requesting* the constant.
  Searches imports and verifies scope using `transitiveImports`.
  -/
  | constant (filepath : FilePath) (name : Name)
  /--
  The transitive closure of imports.
  Required to verify that a fetched constant is actually in scope.
  -/
  | transitiveImports (filepath : FilePath)
  /-- Type of a declaration. Projection from `constant`. -/
  | type (filepath : FilePath) (name : Name)
  /-- Resolve a module name to a file path -/
  | moduleFile (modName : Name)
  /-- All input files in the project -/
  | inputFiles
  /-- Check a file for diagnostics (parsing + elaboration) -/
  | checkFile (filepath : FilePath)
  /-- Check the entire project (all input files) -/
  | checkProject
deriving DecidableEq, Repr, Inhabited, Hashable

def Key.tag : Key → String
  | .text _ => "text"
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
  | .moduleFile _ => "moduleFile"
  | .inputFiles => "inputFiles"
  | .checkFile _ => "checkFile"
  | .checkProject => "checkProject"

abbrev Val : Key → Type
  /- Input query -/
  | .text _ => String
  /-
  Parsing recovers on failure, so this always produces a `Cst`,
  but it may also produce errors.
  -/
  | .cst _ => Cst × Array ParseError
  /- Includes errors from parsing and desugaring -/
  | .astSourceMap _ => Ast × SourceMap × Array Diagnostic
  /- Retain only the `Ast` -/
  | .ast _ => Ast
  /- Retain only the `SourceMap` -/
  | .sourceMap _ => SourceMap
  /- A list of all the imported modules in a file. Never fails. -/
  | .imports _ => Array Name
  /- A map from names to index within the file -/
  | .declarationIndex _ => HashMap Name Nat × Array Diagnostic
  /- The specific AST node and its index -/
  | .declAst _ _ => Option (Ast × Nat)
  /- Full elaboration result for a command at a given index -/
  | .elabCmdAt _ _ => Global × ElabInfo
  /- Full elaboration result: info is always returned, constant only on success -/
  | .elabDecl _ _ => Option (Constant × Origin) × ElabInfo
  /- Semantic projection -/
  | .lookup _ _ => Option (Constant × Origin)
  /- Info projection (always available) -/
  | .lookupInfo _ _ => ElabInfo
  /- The found constant, potentially from an imported file. -/
  | .constant _ _ => Option (Constant × Origin)
  /- The set of all files transitively imported by the given file. -/
  | .transitiveImports _ => HashSet FilePath
  /- The type of the constant, if it was found, retaining only the type -/
  | .type _ _ => Option (Ty 0)
  | .moduleFile _ => Option FilePath
  | .inputFiles => HashSet FilePath
  | .checkFile _ => Array Diagnostic
  | .checkProject => Array Diagnostic

instance {α} [Hashable α] : Hashable (HashMap Name α) where
  hash m := hash <| m.toArray

instance {α} [BEq α] [Hashable α] : Hashable (HashSet α) where
  hash m := hash <| m.toArray

instance : ∀ q, Hashable (Val q) := by
  rintro (_ | _) <;> infer_instance

end Qdt
