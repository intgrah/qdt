module

public import Qdt.Common
public import Qdt.Incremental.Rules

public section

namespace Qdt

open Std (DHashMap)
open System (FilePath)
open Incremental
open Frontend (Path SourceMap Span)

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

def elaborateFile
    {tasks : Tasks config} (b : Build config (DHashMap InputKey InputVal) tasks Id Id)
    (filepath : FilePath) : StateM b.σ (ElabInfo × SourceMap) := do
  let (_, sourceMap, astDiags) ← b.run (Key.astSourceMap filepath)
  let (declIndex, dupDiags) ← b.run (Key.declarationIndex filepath)
  let mut combinedInfo : ElabInfo := 1
  for (name, idx) in declIndex.toList do
    let info : config.R _ ← b.run (Key.lookupInfo filepath name)
    let info : ElabInfo :=
      { info with
        diagnostics := info.diagnostics.map fun d => { d with path := d.path ++ [idx] }
        hovers := info.hovers.map fun h => { h with path := h.path ++ [idx] } }
    combinedInfo := combinedInfo * info
  let allDiags := astDiags ++ dupDiags ++ combinedInfo.diagnostics
  combinedInfo := { combinedInfo with diagnostics := allDiags }
  return (combinedInfo, sourceMap)

def lookupHoverAtPosition (sourceMap : SourceMap) (info : ElabInfo)
    (codepointPos : Nat) : Option (HoverContent × Span) := Id.run do
  let hoverInfos := info.hovers.map fun h => (h.path.reverse, h.hover)

  let some posAstPath := sourceMap.astPathAtPosition codepointPos | return none

  let mut best : Option (Path × HoverContent × Span) := none
  for len in (List.range posAstPath.length).reverse do
    let astPrefix := posAstPath.take (len + 1)
    for (tyPath, hover) in hoverInfos do
      if tyPath == astPrefix then
        if let some span := sourceMap.spanForAstPath astPrefix then
          match best with
          | none => best := some (astPrefix, hover, span)
          | some (prevPath, _, _) =>
              if astPrefix.length > prevPath.length then
                best := some (astPrefix, hover, span)
        break

  match best with
  | none => none
  | some (_, hover, span) => some (hover, span)

end Qdt
