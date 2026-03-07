module

public import Std.Time.DateTime.Timestamp

@[expose] public section

namespace FSWatch

open System (FilePath)

inductive IsDirectory where
  | file
  | directory
deriving Repr, BEq

inductive EventKind where
  | added
  | modified
  | removed
  | movedIn
  | movedOut
  | attributes
  | closeWrite
  | watchedDirRemoved
  | overflow
  | unknown (info : String)
deriving Repr, BEq

structure Event where
  path : FilePath
  time : Std.Time.Timestamp
  isDirectory : IsDirectory
  kind : EventKind
deriving Repr

abbrev EventCallback := Event → IO Unit
abbrev EventPredicate := Event → Bool
abbrev StopListening := IO Unit

namespace EventPredicate
def all : EventPredicate := fun _ => true
def files : EventPredicate := fun e => e.isDirectory == .file
def directories : EventPredicate := fun e => e.isDirectory == .directory
end EventPredicate

end FSWatch
