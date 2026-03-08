module

public import Qdt
public import Qdt.Incremental.Rules

@[expose] public section

namespace Qdt

open Std (DHashMap)
open System (FilePath)
open Incremental
open Incremental.Shake (Store Memo)
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

def elaborateFile (store : Store Key Val) (filepath : FilePath) :
    Option (ElabInfo × SourceMap × Cst) := Id.run do
  let some cstMemo := store.get? (Key.cst filepath) | return none
  let some smMemo := store.get? (Key.astSourceMap filepath) | return none
  let some declMemo := store.get? (Key.declarationIndex filepath) | return none
  let (cst, _) := cstMemo.value
  let (_, sourceMap, _) := smMemo.value
  let (declIndex, dupDiags) := declMemo.value
  let mut combinedInfo : ElabInfo := 1

  for name in declIndex.keysIter do
    if let some infoMemo := store.get? (Key.lookupInfo filepath name) then
      combinedInfo := combinedInfo * infoMemo.value

  let (_, _, astDiags) := smMemo.value
  let allDiags := astDiags ++ dupDiags ++ combinedInfo.diagnostics
  combinedInfo := { combinedInfo with diagnostics := allDiags }

  return some (combinedInfo, sourceMap, cst)

def lookupHoverAtPosition (cst : Cst) (sourceMap : SourceMap) (info : ElabInfo)
    (codepointPos : Nat) : Option HoverContent := Id.run do
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

  return best.map (·.2.2)

end Qdt
