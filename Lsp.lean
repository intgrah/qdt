module

import Lean.Data.Lsp.Communication
import Lean.Data.Lsp.InitShutdown
import Qdt.Common
import Qdt.Lsp

namespace Qdt

open Std (DHashMap HashMap HashSet)
open Lean JsonRpc Lsp
open System (FilePath)
open Incremental
open Frontend (Path SourceMap Span)

def lspBuild : Build config (DHashMap InputKey InputVal) tasks Id Id :=
  SalsaC config Input tasks

def mkRange (text : String) (span : Span) : Range :=
  let fileMap := Lean.FileMap.ofString text
  let startByte := codepointPosToUtf8Pos text span.startPos
  let endByte := codepointPosToUtf8Pos text span.endPos
  {
    start := fileMap.utf8PosToLspPos ⟨startByte⟩
    «end» := fileMap.utf8PosToLspPos ⟨endByte⟩
  }

def mkDiagnostic (text : String) (span : Span) (err : Error) : Lsp.Diagnostic where
  range := mkRange text span
  severity? := some DiagnosticSeverity.error
  source? := some "qdt"
  message := toString err

def mkDiagnosticNoSpan (err : Error) : Lsp.Diagnostic where
  range := { start := ⟨0, 0⟩, «end» := ⟨0, 0⟩ }
  severity? := some DiagnosticSeverity.error
  source? := some "qdt"
  message := toString err

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
  inputs : DHashMap InputKey InputVal
  store : lspBuild.σ

structure ServerState where
  hOut : IO.FS.Stream
  projects : HashMap FilePath ProjectState := ∅
  rootUri? : Option FilePath := none
  shutdownRequested : Bool := false

abbrev ServerM := StateRefT ServerState IO

def ServerM.getProject (filepath : FilePath) : ServerM ProjectState := do
  let st ← get
  let root ← IO.FS.realPath (st.rootUri?.getD (filepath.parent.getD (FilePath.mk ".")))
  match st.projects[root]? with
  | some ps => return ps
  | none =>
      let inputs ← scanInputs root
      let store := lspBuild.init inputs
      let ps : ProjectState := { root, inputs, store }
      modify fun st => { st with projects := st.projects.insert root ps }
      return ps

def ServerM.setProject (ps : ProjectState) : ServerM Unit :=
  modify fun st => { st with projects := st.projects.insert ps.root ps }

def ServerM.writeLsp (msg : JsonRpc.Message) : ServerM Unit := do
  (← get).hOut.writeLspMessage msg

def ServerM.sendResponse (id : RequestID) (result : Json) : ServerM Unit :=
  writeLsp <| Message.response id result

def ServerM.sendError (id : RequestID) (code : ErrorCode) (msg : String) : ServerM Unit :=
  writeLsp <| Message.responseError id code msg none

def ServerM.sendNotification (method : String) (params : Json.Structured) : ServerM Unit :=
  writeLsp <| Message.notification method (some params)

def ServerM.publishDiagnostics
    (uri : DocumentUri)
    (version? : Option Int)
    (diags : Array Lsp.Diagnostic) : ServerM Unit := do
  let params : PublishDiagnosticsParams := { uri, version?, diagnostics := diags }
  match Json.toStructured? params with
  | Except.error e => throw (IO.userError s!"internal error: cannot encode diagnostics: {e}")
  | Except.ok s => sendNotification "textDocument/publishDiagnostics" s

def ServerM.sendFileProgress (uri : DocumentUri) (ranges : Array Range) : ServerM Unit := do
  let processing := ranges.map fun r => Json.mkObj [("range", toJson r)]
  let params := Json.mkObj [
    ("textDocument", Json.mkObj [("uri", toJson uri)]),
    ("processing", toJson processing)
  ]
  match Json.toStructured? params with
  | .ok s => sendNotification "$/lean/fileProgress" s
  | .error _ => pure ()

def buildDiagnostics (text : String) (info : ElabInfo) (sourceMap : SourceMap) : Array Lsp.Diagnostic :=
  info.diagnostics.map fun d =>
    match sourceMap.resolveSpan d.path with
    | some span => mkDiagnostic text span d.error
    | none => mkDiagnosticNoSpan d.error

def runElabTask (ps : ProjectState) (filepath : FilePath) :
    (ElabInfo × SourceMap) × lspBuild.σ :=
  Id.run <| StateT.run (s := ps.store) do
    let _ ← lspBuild.run (Key.checkFile filepath)
    elaborateFile lspBuild filepath

def ServerM.updateFileText (file : FilePath) (text : String) : ServerM Unit := do
  let ps ← getProject file
  let inputs := ps.inputs.insert (.text file) text
  let inputFiles : HashSet FilePath :=
    match ps.inputs.get? .inputFiles with
    | some fs => fs.insert file
    | none => {file}
  let inputs := inputs.insert .inputFiles inputFiles
  let (_, store) := (lspBuild.set (.text file) (some text)).run ps.store
  let (_, store) := (lspBuild.set .inputFiles (some inputFiles)).run store
  setProject { ps with store, inputs }

def ServerM.elaborateAndPublish (file : FilePath) (uri : DocumentUri) (version? : Option Int) : ServerM Unit := do
  let ps ← getProject file
  let text := (ps.inputs.get? (.text file)).getD ""
  let ((info, sourceMap), store') := runElabTask ps file
  setProject { ps with store := store' }
  let diagnostics := buildDiagnostics text info sourceMap
  publishDiagnostics uri version? diagnostics
  sendFileProgress uri #[]

def ServerM.handleInitialize (id : RequestID) (params? : Option Json.Structured) : ServerM Unit := do
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
      change := TextDocumentSyncKind.incremental
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

def ServerM.handleShutdown (id : RequestID) : ServerM Unit := do
  modify fun st => { st with shutdownRequested := true }
  sendResponse id Json.null

def ServerM.handleDidOpen (params? : Option Json.Structured) : ServerM Unit := do
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

def ServerM.handleDidChange (params? : Option Json.Structured) : ServerM Unit := do
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

  let ps ← getProject file
  let mut text := (ps.inputs.get? (.text file)).getD ""
  for change in params.contentChanges do
    match change with
    | .rangeChange range replacement =>
      let fileMap := text.toFileMap
      let start := fileMap.lspPosToUtf8Pos range.start
      let stop := fileMap.lspPosToUtf8Pos range.end
      let pre := String.Pos.Raw.extract text 0 start
      let post := String.Pos.Raw.extract text stop text.rawEndPos
      text := pre ++ replacement ++ post
    | .fullChange newText =>
      text := newText

  updateFileText file text
  elaborateAndPublish file uri version?

def ServerM.handleDidClose (params? : Option Json.Structured) : ServerM Unit := do
  let some params := params?
    | throw (IO.userError "didClose: missing params")
  let params ←
    match fromJson? (α := DidCloseTextDocumentParams) (toJson params) with
    | .ok ps => pure ps
    | .error e => throw (IO.userError s!"didClose: bad params: {e}")
  let uri := params.textDocument.uri
  if let some file ← uriToPath? uri then
    let ps ← getProject file
    let (_, store) := (lspBuild.set (.text file) none).run ps.store
    let inputs := ps.inputs.erase (.text file)
    setProject { ps with store, inputs }
  publishDiagnostics uri none #[]

def ServerM.handleHover (id : RequestID) (params? : Option Json.Structured) : ServerM Unit := do
  let some params := params?
    | throw (IO.userError "hover: missing params")
  let .ok params := fromJson? (α := HoverParams) (toJson params)
    | throw (IO.userError s!"hover: bad params")

  let uri := params.textDocument.uri
  let lspPos := params.position

  let some file ← uriToPath? uri
    | sendResponse id Json.null

  let ps ← getProject file

  let text := (ps.inputs.get? (.text file)).getD ""

  let fileMap := Lean.FileMap.ofString text
  let bytePos := fileMap.lspPosToUtf8Pos lspPos
  let codepointPos := utf8PosToCodepointPos text bytePos.byteIdx

  let ((info, sourceMap), _) := Id.run <| StateT.run (s := ps.store) <| elaborateFile lspBuild file

  let some (hoverContent, span) := lookupHoverAtPosition sourceMap info codepointPos
    | sendResponse id Json.null
  let content := hoverContent.format
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

def ServerM.main (stdin : IO.FS.Stream) : ServerM Unit := do
  while true do
    match ← stdin.readLspMessage with
    | .request id "initialize" params? =>
      try handleInitialize id params?
      catch e => sendError id ErrorCode.internalError s!"initialize failed: {e}"
    | .request id "shutdown" _ =>
      handleShutdown id
    | .request id "textDocument/hover" params? =>
      try handleHover id params?
      catch e => sendError id ErrorCode.internalError s!"hover failed: {e}"
    | .request id method _ =>
      sendError id ErrorCode.methodNotFound s!"unknown method: {method}"
    | .notification "exit" _ => throw (IO.userError "exit")
    | .notification "textDocument/didOpen" params? =>
      handleDidOpen params?
    | .notification "textDocument/didChange" params? =>
      handleDidChange params?
    | .notification "textDocument/didClose" params? => handleDidClose params?
    | _ => continue

end Qdt

open Qdt in
public def main : IO UInt32 := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let st : ServerState := { hOut := stdout }
  try
    (ServerM.main stdin).run' st
    pure 0
  catch e =>
    println! "fatal: {e}"
    pure 1
