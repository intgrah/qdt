module

public import Qdt
public import Qdt.Incremental.Rules

@[expose] public section

namespace Qdt

open Std (DHashMap)
open System (FilePath)
open Incremental
open Frontend (Cst Path SourceMap Span)

def utf8PosToCodepointPos (s : String) (bytePos : Nat) : Nat :=
  go 0 0
where
  go (cp : Nat) (bp : Nat) : Nat :=
    if bp ≥ bytePos then cp
    else if bp < s.utf8ByteSize then
      go (cp + 1) (String.Pos.Raw.next s ⟨bp⟩).byteIdx
    else cp
  partial_fixpoint

def codepointPosToUtf8Pos (s : String) (cpPos : Nat) : Nat :=
  go 0 0
where
  go (cp : Nat) (bp : Nat) : Nat :=
    if cp >= cpPos then bp
    else if bp < s.utf8ByteSize then
      go (cp + 1) (String.Pos.Raw.next s ⟨bp⟩).byteIdx
    else bp

def elaborateFile {ι} [Input InputKey InputV ι]
    (b : Build Monad InputKey InputV Key Val ι)
    (filepath : FilePath) : StateT b.σ (Except BuildError) (ElabInfo × SourceMap × Cst) := do
  let (cst, _) ← b.build tasks (Key.cst filepath)
  let (_, sourceMap, astDiags) ← b.build tasks (Key.astSourceMap filepath)
  let (declIndex, dupDiags) ← b.build tasks (Key.declarationIndex filepath)
  let mut combinedInfo : ElabInfo := 1
  for name in declIndex.keysIter do
    try
      let info ← b.build tasks (Key.lookupInfo filepath name)
      combinedInfo := combinedInfo * info
    catch _ => pure ()
  let allDiags := astDiags ++ dupDiags ++ combinedInfo.diagnostics
  combinedInfo := { combinedInfo with diagnostics := allDiags }
  return (combinedInfo, sourceMap, cst)

def lookupHoverAtPosition (cst : Cst) (sourceMap : SourceMap) (info : ElabInfo)
    (codepointPos : Nat) : Option (HoverContent × Span) := Id.run do
  let cstPath := cst.pathAtPosition codepointPos
  let hoverInfos := info.hovers.map fun h => (h.path.reverse, h.hover)

  let mut best : Option (Path × Path × HoverContent) := none
  for len in (List.range cstPath.length).reverse do
    let cstPrefix := cstPath.take (len + 1)
    if let some astPath := sourceMap.cstToAst[cstPrefix]? then
      for (tyPath, hover) in hoverInfos do
        if tyPath == astPath then
          match best with
          | none => best := some (cstPrefix, astPath, hover)
          | some (_, prevAstPath, _) =>
              if astPath.length > prevAstPath.length then
                best := some (cstPrefix, astPath, hover)
          break

  match best with
  | none => none
  | some (cstPrefix, _, hover) =>
      let span := cst.spanAtPath cstPrefix |>.getD ⟨0, 0⟩
      some (hover, span)

end Qdt
