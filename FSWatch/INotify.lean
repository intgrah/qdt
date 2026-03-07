module

@[expose] public section

namespace FSWatch.INotify

def FD := UInt32
deriving Repr, Inhabited, BEq

def WD := UInt32
deriving Repr, Inhabited, BEq, Hashable

abbrev Mask := UInt32

@[extern "fswatch_IN_ACCESS"] opaque inAccess : Unit → UInt32
@[extern "fswatch_IN_MODIFY"] opaque inModify : Unit → UInt32
@[extern "fswatch_IN_ATTRIB"] opaque inAttrib : Unit → UInt32
@[extern "fswatch_IN_CLOSE_WRITE"] opaque inCloseWrite : Unit → UInt32
@[extern "fswatch_IN_CLOSE_NOWRITE"] opaque inCloseNoWrite : Unit → UInt32
@[extern "fswatch_IN_OPEN"] opaque inOpen : Unit → UInt32
@[extern "fswatch_IN_MOVED_FROM"] opaque inMovedFrom : Unit → UInt32
@[extern "fswatch_IN_MOVED_TO"] opaque inMovedTo : Unit → UInt32
@[extern "fswatch_IN_CREATE"] opaque inCreate : Unit → UInt32
@[extern "fswatch_IN_DELETE"] opaque inDelete : Unit → UInt32
@[extern "fswatch_IN_DELETE_SELF"] opaque inDeleteSelf : Unit → UInt32
@[extern "fswatch_IN_MOVE_SELF"] opaque inMoveSelf : Unit → UInt32
@[extern "fswatch_IN_UNMOUNT"] opaque inUnmount : Unit → UInt32
@[extern "fswatch_IN_Q_OVERFLOW"] opaque inQOverflow : Unit → UInt32
@[extern "fswatch_IN_IGNORED"] opaque inIgnored : Unit → UInt32
@[extern "fswatch_IN_CLOSE"] opaque inClose : Unit → UInt32
@[extern "fswatch_IN_MOVE"] opaque inMove : Unit → UInt32
@[extern "fswatch_IN_ISDIR"] opaque inIsDir : Unit → UInt32
@[extern "fswatch_IN_ALL_EVENTS"] opaque inAllEvents : Unit → UInt32

namespace Mask

def isSet (m : Mask) (flags : UInt32) : Bool :=
  (m &&& flags) != 0

def access : Mask := inAccess ()
def modify : Mask := inModify ()
def attrib : Mask := inAttrib ()
def closeWrite : Mask := inCloseWrite ()
def closeNoWrite : Mask := inCloseNoWrite ()
def openEv : Mask := inOpen ()
def movedFrom : Mask := inMovedFrom ()
def movedTo : Mask := inMovedTo ()
def create : Mask := inCreate ()
def delete : Mask := inDelete ()
def deleteSelf : Mask := inDeleteSelf ()
def moveSelf : Mask := inMoveSelf ()
def unmount : Mask := inUnmount ()
def qOverflow : Mask := inQOverflow ()
def ignored : Mask := inIgnored ()
def close : Mask := inClose ()
def move : Mask := inMove ()
def isDir : Mask := inIsDir ()
def allEvents : Mask := inAllEvents ()
def fileChanges : Mask :=
  create ||| delete ||| modify ||| movedFrom ||| movedTo ||| attrib ||| closeWrite ||| deleteSelf

end Mask

structure RawEvent where
  wd : UInt32
  mask : UInt32
  cookie : UInt32
  name : String
deriving Repr

@[extern "fswatch_inotify_init"]
opaque init : IO FD

@[extern "fswatch_inotify_add_watch"]
opaque addWatch (fd : FD) (path : @& String) (mask : UInt32) : IO WD

@[extern "fswatch_inotify_rm_watch"]
opaque rmWatch (fd : FD) (wd : WD) : IO Unit

@[extern "fswatch_inotify_close"]
opaque close (fd : FD) : IO Unit

@[extern "fswatch_inotify_read"]
opaque read (fd : FD) : IO (Array RawEvent)

end FSWatch.INotify
