import Std.Data.HashMap

import Lean.Data.Json
import Lean.Data.JsonRpc
import Lean.Data.Lsp
import Lean.Data.Lsp.Communication
import Lean.Data.Lsp.Utf16

import Qdt.Config
import Qdt.Error
import Qdt.Frontend.Source
import Qdt.IncrementalElab
import Qdt.Lsp.Hover
import Qdt.Pretty

open Lean JsonRpc Lsp
open System (FilePath)
open Qdt

private def mkRange (text : String) (src : Frontend.Src) : Range :=
  let fileMap := Lean.FileMap.ofString text
  match src with
  | none => { start := ⟨0, 0⟩, «end» := ⟨0, 0⟩ }
  | some span =>
      {
        start := fileMap.utf8PosToLspPos span.startPos
        «end» := fileMap.utf8PosToLspPos span.endPos
      }

private def mkDiagnostic (text : String) (err : Error) : Diagnostic :=
  let src := Error.src err
  {
    range := mkRange text src
    severity? := some DiagnosticSeverity.error
    source? := some "qdt"
    message := toString err
  }

private def uriToPath? (uri : DocumentUri) : IO (Option FilePath) := do
  match System.Uri.fileUriToPath? uri with
  | none => pure none
  | some p =>
      try
        let p ← IO.FS.realPath p
        pure (some p)
      catch _ =>
        pure (some p)

private partial def findTomlUp (dir : FilePath) : Nat → IO (Option FilePath)
  | 0 => pure none
  | fuel + 1 => do
      let candidate := dir / "qdt.toml"
      if ← candidate.pathExists then
        return some candidate
      let parent := dir / ".."
      let parentNorm ← IO.FS.realPath parent
      let dirNorm ← IO.FS.realPath dir
      if parentNorm == dirNorm then
        return none
      findTomlUp parent fuel

private def normaliseConfig (cfg : Config) : IO Config := do
  let cwd ← IO.currentDir
  let root := cfg.projectRoot.getD cwd
  let root ← IO.FS.realPath root
  let srcDirs := cfg.sourceDirectories.map (root / ·)
  let watchDirs := cfg.watchDirs.map (root / ·)
  let deps := cfg.dependencies.map fun d => { d with path := root / d.path }
  return {
    cfg with
    projectRoot := some root
    sourceDirectories := srcDirs
    watchDirs := watchDirs
    dependencies := deps
  }

structure ProjectState where
  config : Config
  engine : Incremental.Engine Error Incremental.Val

structure ServerState where
  projects : Std.HashMap FilePath ProjectState := Std.HashMap.emptyWithCapacity 8
  shutdownRequested : Bool := false

private def getProject (st : ServerState) (file : FilePath) : IO (ServerState × ProjectState) := do
  let dir : FilePath := file.parent.getD (FilePath.mk ".")
  let tomlPath? ← findTomlUp dir 100
  let root0 : FilePath :=
    match tomlPath? with
    | some p => p.parent.getD dir
    | none => dir
  let root ← IO.FS.realPath root0

  match st.projects[root]? with
  | some ps => return (st, ps)
  | none =>
      let cfg ←
        match tomlPath? with
        | some p => Config.fromTomlFile p
        | none => pure { Config.empty with projectRoot := some root }
      let cfg := { cfg with projectRoot := some root }
      let cfg ← normaliseConfig cfg
      let ps : ProjectState := { config := cfg, engine := Incremental.newEngine }
      let st := { st with projects := st.projects.insert root ps }
      return (st, ps)

private def setProject (st : ServerState) (root : FilePath) (ps : ProjectState) : ServerState :=
  { st with projects := st.projects.insert root ps }

private def publishDiagnostics
    (hOut : IO.FS.Stream)
    (uri : DocumentUri)
    (version? : Option Int)
    (diags : Array Diagnostic) : IO Unit := do
  let params : PublishDiagnosticsParams := { uri, version?, diagnostics := diags }
  match Json.toStructured? params with
  | Except.error e => throw (IO.userError s!"internal error: cannot encode diagnostics: {e}")
  | Except.ok s =>
      hOut.writeLspMessage <| Message.notification "textDocument/publishDiagnostics" (some s)

private def handleInitialize (hOut : IO.FS.Stream) (id : RequestID) (params? : Option Json.Structured) : IO Unit := do
  let _params : InitializeParams ←
    match params? with
    | none => throw (IO.userError "initialize: missing params")
    | some p =>
        match (fromJson? (toJson p) : Except String InitializeParams) with
        | Except.ok ps => pure ps
        | Except.error e => throw (IO.userError s!"initialize: bad params: {e}")

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
  hOut.writeLspMessage <| Message.response id (toJson result)

private def handleShutdown (hOut : IO.FS.Stream) (id : RequestID) (stRef : IO.Ref ServerState) : IO Unit := do
  stRef.modify fun st => { st with shutdownRequested := true }
  hOut.writeLspMessage <| Message.response id Json.null

private def handleDidOpen (hOut : IO.FS.Stream) (stRef : IO.Ref ServerState) (params? : Option Json.Structured) : IO Unit := do
  let params ←
    (match params? with
    | none => throw (IO.userError "didOpen: missing params")
    | some p =>
        match (fromJson? (toJson p) : Except String DidOpenTextDocumentParams) with
        | Except.ok ps => pure ps
        | Except.error e => throw (IO.userError s!"didOpen: bad params: {e}")
    : IO DidOpenTextDocumentParams)

  let uri := params.textDocument.uri
  let text := params.textDocument.text
  let version? : Option Int := some (Int.ofNat params.textDocument.version)

  let some file ← uriToPath? uri
    | publishDiagnostics hOut uri version? #[
        {
          range := { start := ⟨0, 0⟩, «end» := ⟨0, 0⟩ }
          severity? := some DiagnosticSeverity.error
          source? := some "qdt"
          message := s!"unsupported URI: {uri}"
          : Diagnostic
        }
      ]
      return

  Incremental.setFileTextOverride file text

  let st ← stRef.get
  let (st, ps) ← getProject st file
  stRef.set st

  let task : Incremental.TaskM Error Incremental.Val Incremental.GlobalEnv :=
    Incremental.TaskM.fetch (Incremental.Key.elabModule file)

  match ← Incremental.run ps.config ps.engine task with
  | Except.ok (_, engine') =>
      let ps' : ProjectState := { ps with engine := engine' }
      let root := ps.config.projectRoot.getD (file.parent.getD (FilePath.mk "."))
      stRef.modify fun st => setProject st root ps'
      publishDiagnostics hOut uri version? #[]
  | Except.error err =>
      let diag := mkDiagnostic text err
      publishDiagnostics hOut uri version? #[diag]

private def handleDidChange (hOut : IO.FS.Stream) (stRef : IO.Ref ServerState) (params? : Option Json.Structured) : IO Unit := do
  let params ←
    match params? with
    | none => throw (IO.userError "didChange: missing params")
    | some p =>
        match fromJson? (α := DidChangeTextDocumentParams) (toJson p) with
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
  Incremental.setFileTextOverride file text

  let st ← stRef.get
  let (st, ps) ← getProject st file
  stRef.set st

  let task : Incremental.TaskM Error Incremental.Val Incremental.GlobalEnv :=
    Incremental.TaskM.fetch (Incremental.Key.elabModule file)

  match ← Incremental.run ps.config ps.engine task with
  | Except.ok (_, engine') =>
      let ps' : ProjectState := { ps with engine := engine' }
      let root := ps.config.projectRoot.getD (file.parent.getD (FilePath.mk "."))
      stRef.modify fun st => setProject st root ps'
      publishDiagnostics hOut uri version? #[]
  | Except.error err =>
      let diag := mkDiagnostic text err
      publishDiagnostics hOut uri version? #[diag]

private def handleDidClose (hOut : IO.FS.Stream) (params? : Option Json.Structured) : IO Unit := do
  let params ←
    match params? with
    | none => throw (IO.userError "didClose: missing params")
    | some p =>
        match fromJson? (α := DidCloseTextDocumentParams) (toJson p) with
        | .ok ps => pure ps
        | .error e => throw (IO.userError s!"didClose: bad params: {e}")
  let uri := params.textDocument.uri
  if let some file ← uriToPath? uri then
    Incremental.eraseFileTextOverride file
  publishDiagnostics hOut uri none #[]

private def handleHover
    (hOut : IO.FS.Stream)
    (id : RequestID)
    (stRef : IO.Ref ServerState)
    (params? : Option Json.Structured) : IO Unit := do
  let params ←
    match params? with
    | none => throw (IO.userError "hover: missing params")
    | some p =>
        match fromJson? (α := HoverParams) (toJson p) with
        | .ok ps => pure ps
        | .error e => throw (IO.userError s!"hover: bad params: {e}")

  let uri := params.textDocument.uri
  let lspPos := params.position

  let some file ← uriToPath? uri
    | do hOut.writeLspMessage <| Message.response id Json.null
         return

  let text ← Incremental.getFileText file
  let fileMap := Lean.FileMap.ofString text
  let bytePos := fileMap.lspPosToUtf8Pos lspPos

  let st ← stRef.get
  let (st, ps) ← getProject st file
  stRef.set st

  let task : Incremental.TaskM Error Incremental.Val Incremental.GlobalEnv :=
    Incremental.TaskM.fetch (Incremental.Key.elabModule file)

  match ← Incremental.run ps.config ps.engine task with
  | .error _ =>
      hOut.writeLspMessage <| Message.response id Json.null
  | .ok (globalEnv, engine') =>
      let ps' : ProjectState := { ps with engine := engine' }
      let root := ps.config.projectRoot.getD (file.parent.getD (FilePath.mk "."))
      stRef.modify fun st => setProject st root ps'

      match ← Lsp.findHoverInGlobal file.toString bytePos globalEnv with
      | none =>
          hOut.writeLspMessage <| Message.response id Json.null
      | some (_name, result) =>
          let range := mkRange text (some result.span)
          let content : MarkupContent := {
            kind := MarkupKind.markdown
            value := s!"```qdt\n{result.contents}\n```"
          }
          let hover : Hover := {
            contents := content
            range? := some range
          }
          hOut.writeLspMessage <| Message.response id (toJson hover)

partial def mainLoop (hIn hOut : IO.FS.Stream) (stRef : IO.Ref ServerState) : IO Unit := do
  while true do
    let msg ← hIn.readLspMessage
    match msg with
    | .request id method params? =>
        match method with
        | "initialize" =>
            try
              handleInitialize hOut id params?
            catch e =>
              hOut.writeLspMessage <|
                Message.responseError id ErrorCode.internalError s!"initialize failed: {e}" none
        | "shutdown" =>
            handleShutdown hOut id stRef
        | "textDocument/hover" =>
            try
              handleHover hOut id stRef params?
            catch e =>
              hOut.writeLspMessage <|
                Message.responseError id ErrorCode.internalError s!"hover failed: {e}" none
        | _ =>
            hOut.writeLspMessage <|
              Message.responseError id ErrorCode.methodNotFound s!"unknown method: {method}" none
    | .notification method params? =>
        match method with
        | "exit" => throw (IO.userError "exit")
        | "textDocument/didOpen" =>
            try handleDidOpen hOut stRef params? catch _ => pure ()
        | "textDocument/didChange" =>
            try handleDidChange hOut stRef params? catch _ => pure ()
        | "textDocument/didClose" =>
            try handleDidClose hOut params? catch _ => pure ()
        | _ => pure ()
    | _ => pure ()

def main : IO UInt32 := do
  let hIn ← IO.getStdin
  let hOut ← IO.getStdout
  let stRef ← IO.mkRef { : ServerState}
  try
    mainLoop hIn hOut stRef
    pure 0
  finally
    pure 0
