module

public import Qdt.Cli
public import Incremental.Busy
public import Incremental.Salsa
public import Incremental.Shake
public import Qdt.Incremental.Query

@[expose] public section

namespace Qdt

open Std (DHashMap HashSet)
open System (FilePath)
open Incremental

abbrev Input := DHashMap InputKey InputVal

def selectBuild : BuildSystem → Build Monad InputKey InputV Key Val Input
  | .busy => Busy InputKey InputV Key Val Input
  | .lessBusy => LessBusy InputKey InputV Key Val Input
  | .salsa => Salsa InputKey InputV Key Val Input
  | .shake => Shake InputKey InputV Key Val Input
  | .shakeNative => ShakeNative InputKey InputV Key Val Input

partial def listSrcFiles (dir : FilePath) : IO (List FilePath) := do
  let mut result : List FilePath := []
  if ← dir.isDir then
    let entries ← dir.readDir
    for entry in entries do
      let path := entry.path
      if ← path.isDir then
        result := result ++ (← listSrcFiles path)
      else if path.extension == some "qdt" then
        result := path :: result
  return result

def scanInputs (root : FilePath) : IO (DHashMap InputKey InputVal) := do
  let rawFiles ← listSrcFiles root
  let mut inputs : DHashMap InputKey InputVal := DHashMap.emptyWithCapacity 64
  let mut inputFiles : HashSet FilePath := ∅
  for file in rawFiles do
    let absPath ← IO.FS.realPath file
    inputFiles := inputFiles.insert absPath
    let text ← IO.FS.readFile absPath
    inputs := inputs.insert (.text absPath) text
  inputs := inputs.insert .inputFiles inputFiles
  return inputs

end Qdt
