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
      let bytePos := Frontend.codepointPosToUtf8Pos text span.startPos
      let ⟨line, col⟩ := posToLineCol text bytePos
      s!"{file}:{line}:{col + 1}: error: {d.error.format}"
  | none =>
      s!"{file}: error: {d.error.format}"

end Qdt.Cli
