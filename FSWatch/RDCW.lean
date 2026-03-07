module

@[expose] public section

namespace FSWatch.RDCW

abbrev Handle := USize

structure Filter where
  val : UInt32
deriving Repr, Inhabited, BEq

instance : OrOp Filter where
  or a b := ⟨a.val ||| b.val⟩

@[extern "fswatch_FILE_NOTIFY_CHANGE_FILE_NAME"] opaque fileNotifyChangeFileName : Unit → UInt32
@[extern "fswatch_FILE_NOTIFY_CHANGE_DIR_NAME"] opaque fileNotifyChangeDirName : Unit → UInt32
@[extern "fswatch_FILE_NOTIFY_CHANGE_ATTRIBUTES"] opaque fileNotifyChangeAttributes : Unit → UInt32
@[extern "fswatch_FILE_NOTIFY_CHANGE_SIZE"] opaque fileNotifyChangeSize : Unit → UInt32
@[extern "fswatch_FILE_NOTIFY_CHANGE_LAST_WRITE"] opaque fileNotifyChangeLastWrite : Unit → UInt32
@[extern "fswatch_FILE_NOTIFY_CHANGE_SECURITY"] opaque fileNotifyChangeSecurity : Unit → UInt32

namespace Filter
def fileName : Filter := ⟨fileNotifyChangeFileName ()⟩
def dirName : Filter := ⟨fileNotifyChangeDirName ()⟩
def attributes : Filter := ⟨fileNotifyChangeAttributes ()⟩
def size : Filter := ⟨fileNotifyChangeSize ()⟩
def lastWrite : Filter := ⟨fileNotifyChangeLastWrite ()⟩
def security : Filter := ⟨fileNotifyChangeSecurity ()⟩
def fileChanges : Filter := fileName ||| dirName ||| attributes ||| size ||| lastWrite
end Filter

@[extern "fswatch_FILE_ACTION_ADDED"] opaque fileActionAdded : Unit → UInt32
@[extern "fswatch_FILE_ACTION_REMOVED"] opaque fileActionRemoved : Unit → UInt32
@[extern "fswatch_FILE_ACTION_MODIFIED"] opaque fileActionModified : Unit → UInt32
@[extern "fswatch_FILE_ACTION_RENAMED_OLD_NAME"] opaque fileActionRenamedOldName : Unit → UInt32
@[extern "fswatch_FILE_ACTION_RENAMED_NEW_NAME"] opaque fileActionRenamedNewName : Unit → UInt32

namespace Action
def added : Nat := (fileActionAdded ()).toNat
def removed : Nat := (fileActionRemoved ()).toNat
def modified : Nat := (fileActionModified ()).toNat
def renamedOld : Nat := (fileActionRenamedOldName ()).toNat
def renamedNew : Nat := (fileActionRenamedNewName ()).toNat
end Action

structure RawEvent where
  action : Nat
  name : String
deriving Repr

@[extern "fswatch_rdcw_open"]
opaque openDir (path : @& String) : IO Handle

@[extern "fswatch_rdcw_close"]
opaque close (h : Handle) : IO Unit

@[extern "fswatch_rdcw_read"]
opaque read (h : Handle) (watchSubTree : UInt8) (filter : UInt32) : IO (Array RawEvent)

end FSWatch.RDCW
