module

@[expose] public section

namespace Qdt

open System (FilePath)

structure Config where
  root : FilePath
  watchMode : Bool := false
deriving Repr

namespace Config

def moduleToPath (modName : String) : FilePath :=
  let parts := modName.splitOn "."
  let pathStr := String.intercalate "/" parts
  FilePath.mk pathStr |>.addExtension "qdt"

end Config

end Qdt
