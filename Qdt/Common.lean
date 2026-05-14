module

public import Qdt.Cli
public import Incremental.Busy
public import Incremental.LessBusy
public import Incremental.Salsa
public import Incremental.SalsaC
public import Incremental.Shake.Standard
public import Incremental.Shake.Store
public import Incremental.Shake.C
public import Incremental.Shake.Rdeps
public import Qdt.Incremental.Query

@[expose] public section

namespace Qdt

open Std (DHashMap HashSet)
open System (FilePath)
open Incremental

abbrev Input := DHashMap InputKey InputVal

instance : Incremental.Input config Input where
  get := DHashMap.get?
  set m i v := m.alter i (fun _ => v)
  get_set_self _ _ _ := DHashMap.get?_alter_self
  get_set_other _ _ _ _ h := by grind

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
