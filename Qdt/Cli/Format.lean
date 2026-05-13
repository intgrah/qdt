module

public import Qdt.Incremental.Rules

@[expose] public section

namespace Qdt.Cli

open System (FilePath)

def posToLineCol (text : String) (pos : Nat) : Lean.Position :=
  (Lean.FileMap.ofString text).toPosition ⟨pos⟩

def Diagnostic.format (file : FilePath) (text : String) (sm : Frontend.SourceMap)
    (d : Diagnostic) : String :=
  match sm.resolveSpan d.path with
  | some span =>
      let ⟨line, col⟩ := posToLineCol text span.startPos
      s!"{file}:{line}:{col}: error: {d.error}"
  | none =>
      s!"{file}: error: {d.error}"

end Qdt.Cli
