module

public import Qdt.Incremental.Rules
public import Lean.Data.Lsp.Communication
public import Lean.Data.Lsp.InitShutdown

@[expose] public section

namespace Qdt

open Std (DHashMap HashMap)
open Lean JsonRpc Lsp
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

def mkRange (text : String) (span : Span) : Range :=
  let fileMap := Lean.FileMap.ofString text
  let startByte := codepointPosToUtf8Pos text span.startPos
  let endByte := codepointPosToUtf8Pos text span.endPos
  {
    start := fileMap.utf8PosToLspPos ⟨startByte⟩
    «end» := fileMap.utf8PosToLspPos ⟨endByte⟩
  }

def mkDiagnostic (text : String) (span : Span) (err : Error) : Lsp.Diagnostic :=
  {
    range := mkRange text span
    severity? := some DiagnosticSeverity.error
    source? := some "qdt"
    message := toString err
  }

def mkDiagnosticNoSpan (err : Error) : Lsp.Diagnostic :=
  {
    range := { start := ⟨0, 0⟩, «end» := ⟨0, 0⟩ }
    severity? := some DiagnosticSeverity.error
    source? := some "qdt"
    message := toString err
  }

def uriToPath? (uri : DocumentUri) : IO (Option FilePath) := do
  match System.Uri.fileUriToPath? uri with
  | none => pure none
  | some p =>
      try
        some <$> IO.FS.realPath p
      catch _ =>
        pure (some p)

structure ProjectState where
  root : FilePath
  store : Store Key Val

structure ServerState where
  hOut : IO.FS.Stream
  projects : HashMap FilePath ProjectState := ∅
  rootUri? : Option FilePath := none
  shutdownRequested : Bool := false

abbrev ServerM := StateRefT ServerState IO

def getProject (filepath : FilePath) : ServerM ProjectState := do
  let st ← get
  let root ← IO.FS.realPath (st.rootUri?.getD (filepath.parent.getD (FilePath.mk ".")))
  match st.projects[root]? with
  | some ps => return ps
  | none =>
      let ps : ProjectState := { root, store := DHashMap.emptyWithCapacity 1024 }
      modify fun st => { st with projects := st.projects.insert root ps }
      return ps

def setProject (ps : ProjectState) : ServerM Unit :=
  modify fun st => { st with projects := st.projects.insert ps.root ps }

def writeLsp (msg : JsonRpc.Message) : ServerM Unit := do
  (← get).hOut.writeLspMessage msg

def sendResponse (id : RequestID) (result : Json) : ServerM Unit :=
  writeLsp <| Message.response id result

def sendError (id : RequestID) (code : ErrorCode) (msg : String) : ServerM Unit :=
  writeLsp <| Message.responseError id code msg none

def sendNotification (method : String) (params : Json.Structured) : ServerM Unit :=
  writeLsp <| Message.notification method (some params)

def publishDiagnostics
    (uri : DocumentUri)
    (version? : Option Int)
    (diags : Array Lsp.Diagnostic) : ServerM Unit := do
  let params : PublishDiagnosticsParams := { uri, version?, diagnostics := diags }
  match Json.toStructured? params with
  | Except.error e => throw (IO.userError s!"internal error: cannot encode diagnostics: {e}")
  | Except.ok s => sendNotification "textDocument/publishDiagnostics" s

def sendFileProgress (uri : DocumentUri) (ranges : Array Range) : ServerM Unit := do
  let processing := ranges.map fun r => Json.mkObj [("range", toJson r)]
  let params := Json.mkObj [
    ("textDocument", Json.mkObj [("uri", toJson uri)]),
    ("processing", toJson processing)
  ]
  match Json.toStructured? params with
  | .ok s => sendNotification "$/lean/fileProgress" s
  | .error _ => pure ()

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

def buildDiagnostics (text : String) (info : ElabInfo) (sourceMap : SourceMap) (cst : Cst) : Array Lsp.Diagnostic :=
  info.diagnostics.map fun d =>
    let astPathFwd := d.path.reverse
    let cstPath? := Id.run do
      for len in (List.range astPathFwd.length).reverse do
        let astPrefix := astPathFwd.take (len + 1)
        if let some cstPath := sourceMap.astToCst[astPrefix]? then
          return some cstPath
      return none
    let span? :=
      match cstPath? with
      | some cstPath => cst.spanAtPath cstPath
      | none =>
          if !d.path.isEmpty then cst.spanAtPath d.path
          else none
    match span? with
    | some span => mkDiagnostic text span d.error
    | none => mkDiagnosticNoSpan d.error

def runElabTask (ps : ProjectState) (filepath : FilePath) :
    IO ((ElabInfo × SourceMap × Cst) × Store Key Val) := do
  let store ← Store.populate ps.root ps.store
  let store ← match ShakeNative.build tasks (Key.checkFile filepath) store with
    | .ok (_, s) => pure s
    | .error .cycle => throw (IO.userError "cycle detected")
    | .error .missingInput => throw (IO.userError "missing input")
  match elaborateFile store filepath with
  | some result => pure (result, store)
  | none => throw (IO.userError "elaboration failed")

def updateFileText (file : FilePath) (text : String) : ServerM Unit := do
  let ps ← getProject file
  let memo : Memo Key Val (.text file) := { value := text, deps := ∅ }
  setProject { ps with store := ps.store.insert (.text file) memo }

def elaborateAndPublish (file : FilePath) (uri : DocumentUri) (version? : Option Int) : ServerM Unit := do
  let ps ← getProject file
  let text := match ps.store.get? (.text file) with
    | some memo => memo.value
    | none => ""
  let ((info, sourceMap, cst), store') ← runElabTask ps file
  setProject { ps with store := store' }
  let diagnostics := buildDiagnostics text info sourceMap cst
  publishDiagnostics uri version? diagnostics
  sendFileProgress uri #[]

def handleInitialize (id : RequestID) (params? : Option Json.Structured) : ServerM Unit := do
  let some params := params?
    | throw (IO.userError "initialize: missing params")
  let initParams : InitializeParams ←
    match fromJson? (α := InitializeParams) (toJson params) with
    | .ok ps => pure ps
    | Except.error e => throw (IO.userError s!"initialize: bad params: {e}")
  if let some rootUri := initParams.rootUri? then
    if let some rootPath ← uriToPath? rootUri then
      modify fun st => { st with rootUri? := some rootPath }

  let sync : TextDocumentSyncOptions :=
    {
      openClose := true
      change := TextDocumentSyncKind.full
      willSave := false
      willSaveWaitUntil := false
      save? := none
    }

  let caps : ServerCapabilities := {
    textDocumentSync? := some sync
    hoverProvider := true
  }
  let result : InitializeResult := {
    capabilities := caps
    serverInfo? := some { name := "qdt-lsp", version? := some "0.1.0" }
  }
  sendResponse id (toJson result)

def handleShutdown (id : RequestID) : ServerM Unit := do
  modify fun st => { st with shutdownRequested := true }
  sendResponse id Json.null

def handleDidOpen (params? : Option Json.Structured) : ServerM Unit := do
  let some params := params?
    | throw (IO.userError "didOpen: missing params")
  let params ←
    match fromJson? (α := DidOpenTextDocumentParams) (toJson params) with
    | .ok ps => pure ps
    | .error e => throw (IO.userError s!"didOpen: bad params: {e}")

  let uri := params.textDocument.uri
  let text := params.textDocument.text
  let version? : Option Int := some (Int.ofNat params.textDocument.version)

  let some file ← uriToPath? uri
    | publishDiagnostics uri version? #[
        {
          range := { start := ⟨0, 0⟩, «end» := ⟨0, 0⟩ }
          severity? := some DiagnosticSeverity.error
          source? := some "qdt"
          message := s!"unsupported URI: {uri}"
          : Lsp.Diagnostic
        }
      ]
      return

  updateFileText file text
  elaborateAndPublish file uri version?

def handleDidChange (params? : Option Json.Structured) : ServerM Unit := do
  let some params := params?
    | throw (IO.userError "didChange: missing params")
  let params ←
    match fromJson? (α := DidChangeTextDocumentParams) (toJson params) with
    | .ok ps => pure ps
    | .error e => throw (IO.userError s!"didChange: bad params: {e}")

  let uri := params.textDocument.uri
  let version? : Option Int := params.textDocument.version?.map Int.ofNat

  let some file ← uriToPath? uri
    | return

  let text? : Option String :=
    match params.contentChanges.back? with
    | some (.fullChange text) => some text
    | _ => none
  let some text := text? | return

  updateFileText file text
  elaborateAndPublish file uri version?

def handleDidClose (params? : Option Json.Structured) : ServerM Unit := do
  let some params := params?
    | throw (IO.userError "didClose: missing params")
  let params ←
    match fromJson? (α := DidCloseTextDocumentParams) (toJson params) with
    | .ok ps => pure ps
    | .error e => throw (IO.userError s!"didClose: bad params: {e}")
  let uri := params.textDocument.uri
  if let some file ← uriToPath? uri then
    let ps ← getProject file
    setProject { ps with store := ps.store.erase (.text file) }
  publishDiagnostics uri none #[]

def handleHover (id : RequestID) (params? : Option Json.Structured) : ServerM Unit := do
  let some params := params?
    | throw (IO.userError "hover: missing params")
  let params ←
    match fromJson? (α := HoverParams) (toJson params) with
    | .ok ps => pure ps
    | .error e => throw (IO.userError s!"hover: bad params: {e}")

  let uri := params.textDocument.uri
  let lspPos := params.position

  let some file ← uriToPath? uri
    | sendResponse id Json.null

  let ps ← getProject file

  let text ←
    match ps.store.get? (.text file) with
    | some memo => pure memo.value
    | none => IO.FS.readFile file

  let fileMap := Lean.FileMap.ofString text
  let bytePos := fileMap.lspPosToUtf8Pos lspPos
  let codepointPos := utf8PosToCodepointPos text bytePos.byteIdx

  let ((info, sourceMap, cst), store') ← runElabTask ps file
  setProject { ps with store := store' }

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
  | none =>
      sendResponse id Json.null
  | some (cstPath, _, hover) =>
      let span := cst.spanAtPath cstPath |>.getD ⟨0, 0⟩
      let content := hover.format
      let range := mkRange text span
      let markupContent : MarkupContent := {
        kind := MarkupKind.markdown
        value := s!"```qdt\n{content}\n```"
      }
      let hover : Hover := {
        contents := markupContent
        range? := some range
      }
      sendResponse id (toJson hover)

def mainLoop (stdin : IO.FS.Stream) : ServerM Unit := do
  while true do
    match ← stdin.readLspMessage with
    | .request id method params? =>
      match method with
      | "initialize" =>
        try handleInitialize id params?
        catch e => sendError id ErrorCode.internalError s!"initialize failed: {e}"
      | "shutdown" => handleShutdown id
      | "textDocument/hover" =>
        try handleHover id params?
        catch e => sendError id ErrorCode.internalError s!"hover failed: {e}"
      | _ =>
        sendError id ErrorCode.methodNotFound s!"unknown method: {method}"
    | .notification method params? =>
      match method with
      | "exit" => throw (IO.userError "exit")
      | "textDocument/didOpen" =>
        try handleDidOpen params? catch _ => pure ()
      | "textDocument/didChange" =>
        try handleDidChange params? catch _ => pure ()
      | "textDocument/didClose" =>
        try handleDidClose params? catch _ => pure ()
      | _ => continue
    | _ => continue

end Qdt

open Qdt in
def main : IO UInt32 := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let st : ServerState := { hOut := stdout }
  try
    (mainLoop stdin).run' st
    pure 0
  catch e =>
    println!"fatal: {e}"
    pure 1
