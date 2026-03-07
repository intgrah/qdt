module

public import FSWatch.Types
public import FSWatch.INotify
public import FSWatch.RDCW

@[expose] public section

namespace FSWatch

open System (FilePath)

structure WatchEntry where
  path : FilePath
  callback : EventCallback
  predicate : EventPredicate
  onNewDir : Option (FilePath → IO Unit) := none

structure Manager where
  mk ::
  linuxFd : Option INotify.FD
  watches : IO.Ref (Array WatchEntry)
  linuxWds : IO.Ref (Array (INotify.WD × Nat))
  windowsHandles : IO.Ref (Array (RDCW.Handle × Nat))
  running : IO.Ref Bool
  task : IO.Ref (Option (Task (Except IO.Error Unit)))

namespace Manager

def convertINotifyEvent (basePath : FilePath) (time : Std.Time.Timestamp)
    (raw : INotify.RawEvent) : Event :=
  let name := if raw.name.isEmpty then "" else raw.name
  let path : FilePath := if name.isEmpty then basePath else basePath / name
  let isDir : IsDirectory :=
    if INotify.Mask.isDir.isSet raw.mask then .directory else .file
  let kind : EventKind :=
    if INotify.Mask.create.isSet raw.mask then .added
    else if INotify.Mask.modify.isSet raw.mask then .modified
    else if INotify.Mask.delete.isSet raw.mask then .removed
    else if INotify.Mask.movedFrom.isSet raw.mask then .movedOut
    else if INotify.Mask.movedTo.isSet raw.mask then .movedIn
    else if INotify.Mask.attrib.isSet raw.mask then .attributes
    else if INotify.Mask.closeWrite.isSet raw.mask then .closeWrite
    else if INotify.Mask.deleteSelf.isSet raw.mask then .watchedDirRemoved
    else if INotify.Mask.qOverflow.isSet raw.mask then .overflow
    else .unknown s!"mask={raw.mask}"
  { path, time, isDirectory := isDir, kind }

def convertRDCWEvent (basePath : FilePath) (time : Std.Time.Timestamp)
    (raw : RDCW.RawEvent) : Event :=
  let path : FilePath := basePath / raw.name
  let kind : EventKind :=
    if raw.action == RDCW.Action.added then .added
    else if raw.action == RDCW.Action.removed then .removed
    else if raw.action == RDCW.Action.modified then .modified
    else if raw.action == RDCW.Action.renamedOld then .movedOut
    else if raw.action == RDCW.Action.renamedNew then .movedIn
    else .unknown s!"action={raw.action}"
  { path, time, isDirectory := .file, kind }

def linuxLoop (m : Manager) : IO Unit := do
  let some fd := m.linuxFd | return
  while ← m.running.get do
    let rawEvents ← INotify.read fd
    let time ← Std.Time.Timestamp.now
    let wds ← m.linuxWds.get
    let watches ← m.watches.get
    for raw in rawEvents do
      if let some idx := wds.toList.lookup raw.wd then
        if let some entry := watches[idx]? then
          let event := convertINotifyEvent entry.path time raw
          if entry.predicate event then
            try entry.callback event catch _ => pure ()
          if event.kind == .added && event.isDirectory == .directory then
            if let some onNewDir := entry.onNewDir then
              try onNewDir event.path catch _ => pure ()
          if event.kind == .movedIn && event.isDirectory == .directory then
            if let some onNewDir := entry.onNewDir then
              try onNewDir event.path catch _ => pure ()
    IO.sleep 10

def windowsLoop (m : Manager) : IO Unit := do
  while ← m.running.get do
    let handles ← m.windowsHandles.get
    let watches ← m.watches.get
    for (handle, idx) in handles do
      if hBound : idx < watches.size then
        let entry := watches[idx]
        let rawEvents ← RDCW.read handle 0 RDCW.Filter.fileChanges
        let time ← Std.Time.Timestamp.now
        for raw in rawEvents do
          let event := convertRDCWEvent entry.path time raw
          if entry.predicate event then
            try entry.callback event catch _ => pure ()

def create : IO Manager := do
  let linuxFd ← if System.Platform.isWindows then pure none else some <$> INotify.init
  let watches ← IO.mkRef #[]
  let linuxWds ← IO.mkRef #[]
  let windowsHandles ← IO.mkRef #[]
  let running ← IO.mkRef true
  let task ← IO.mkRef none
  let m : Manager := { linuxFd, watches, linuxWds, windowsHandles, running, task }
  let t ← IO.asTask do
    if System.Platform.isWindows then windowsLoop m else linuxLoop m
  m.task.set (some t)
  return m

def stop (m : Manager) : IO Unit := do
  m.running.set false
  if let some t := ← m.task.get then
    let _ ← IO.wait t
  if let some fd := m.linuxFd then
    let wds ← m.linuxWds.get
    for (wd, _) in wds do
      try INotify.rmWatch fd wd catch _ => pure ()
    INotify.close fd
  let handles ← m.windowsHandles.get
  for (h, _) in handles do
    try RDCW.close h catch _ => pure ()

def addSingleWatch (m : Manager) (absPath : FilePath) (idx : Nat) : IO StopListening := do
  if System.Platform.isWindows then
    let h ← RDCW.openDir absPath.toString
    m.windowsHandles.modify (·.push (h, idx))
    return do
      m.windowsHandles.modify (·.filter (·.2 != idx))
      try RDCW.close h catch _ => pure ()
  else
    let some fd := m.linuxFd | throw (IO.userError "Manager not initialized")
    let wd ← INotify.addWatch fd absPath.toString INotify.Mask.fileChanges
    m.linuxWds.modify (·.push (wd, idx))
    return do
      m.linuxWds.modify (·.filter (·.2 != idx))
      try INotify.rmWatch fd wd catch _ => pure ()

def watchDir (m : Manager) (path : FilePath)
    (predicate : EventPredicate := EventPredicate.all)
    (callback : EventCallback) : IO StopListening := do
  let absPath ← IO.FS.realPath path
  let idx := (← m.watches.get).size
  let entry : WatchEntry := { path := absPath, callback, predicate }
  m.watches.modify (·.push entry)
  addSingleWatch m absPath idx

partial def watchTree (m : Manager) (path : FilePath)
    (predicate : EventPredicate := EventPredicate.all)
    (callback : EventCallback) : IO StopListening := do
  let absPath ← IO.FS.realPath path
  let stops ← IO.mkRef ([] : List StopListening)

  let rec addDir (dir : FilePath) : IO Unit := do
    let idx := (← m.watches.get).size
    let entry : WatchEntry := { path := dir, callback, predicate, onNewDir := some addDir }
    m.watches.modify (·.push entry)
    let stop ← addSingleWatch m dir idx
    stops.modify (stop :: ·)
    for child in ← dir.readDir do
      if (← child.path.isDir) then
        addDir child.path

  addDir absPath
  return do
    for stop in ← stops.get do stop

def withManager {α} (f : Manager → IO α) : IO α := do
  let m ← create
  try f m finally stop m

end Manager
end FSWatch
