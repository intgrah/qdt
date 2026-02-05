import Std.Data.HashMap

import Lean.Data.Json
import Lean.Data.JsonRpc
import Lean.Data.Lsp
import Lean.Data.Lsp.Communication
import Lean.Data.Lsp.Utf16

import Qdt.Config
import Qdt.Error
import Qdt.Frontend.Source
import Qdt.Incremental
import Qdt.Lsp.Hover
import Qdt.Pretty

open Std (HashMap)
open Lean JsonRpc Lsp
open System (FilePath)
open Qdt
open Incremental (Engine fetchQ Key TaskM Val)

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

private def findTomlUp (dir : FilePath) : Nat → IO (Option FilePath)
  | 0 => return none
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
  return {
    cfg with
    projectRoot := some root
    sourceDirectories := srcDirs
    watchDirs := watchDirs
  }

structure ProjectState where
  config : Config
  engine : Engine Error Val
  overrides : HashMap FilePath String

structure ServerState where
  projects : HashMap FilePath ProjectState := ∅
  shutdownRequested : Bool := false

private def getProject (st : ServerState) (filepath : FilePath) : IO (ServerState × ProjectState) := do
  let dir : FilePath := filepath.parent.getD (FilePath.mk ".")
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
      let ps : ProjectState := { config := cfg, engine := Incremental.newEngine, overrides := ∅ }
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

partial def buildEnv (filepath : FilePath) : TaskM Error Val Global := do
  let mut globalEnv : Global := HashMap.emptyWithCapacity 4096
  let importNames ← fetchQ (Key.moduleImports filepath)
  for modName in importNames.toArray do
    match ← fetchQ (Key.moduleFile modName) with
    | none => throw (.msg s!"Import not found: {modName}")
    | some depFile =>
        let depEnv ← buildEnv depFile
        for (n, e) in depEnv.toList.toArray do
          globalEnv := globalEnv.insert n e
  let ordering : List Incremental.TopDecl ← fetchQ (Key.declOrdering filepath)
  for decl in ordering do
    let localEnv : Global ← fetchQ (Key.elabTop filepath decl)
    for (n, e) in localEnv.toList.toArray do
      globalEnv := globalEnv.insert n e
  return globalEnv

private def handleInitialize (hOut : IO.FS.Stream) (id : RequestID) (params? : Option Json.Structured) : IO Unit := do
  let some params := params?
    | throw (IO.userError "initialize: missing params")
  let _params : InitializeParams ←
    match fromJson? (α := InitializeParams) (toJson params) with
    | .ok ps => pure ps
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

  let st ← stRef.get
  let (st, ps) ← getProject st file

  let overrides := ps.overrides.insert file text
  let ps := { ps with overrides }
  stRef.set st

  let task : TaskM Error Val Global := buildEnv file
  let ctx : Incremental.Context := { config := ps.config, overrides := ps.overrides }

  match ← (Incremental.run ctx ps.engine task).toIO' with
  | .ok (_, engine') =>
      let ps' : ProjectState := { ps with engine := engine' }
      let root := ps.config.projectRoot.getD (file.parent.getD (FilePath.mk "."))
      stRef.modify fun st => setProject st root ps'
      publishDiagnostics hOut uri version? #[]
  | Except.error err =>
      let diag := mkDiagnostic text err
      publishDiagnostics hOut uri version? #[diag]

private def handleDidChange (hOut : IO.FS.Stream) (stRef : IO.Ref ServerState) (params? : Option Json.Structured) : IO Unit := do
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
  let st ← stRef.get
  let (st, ps) ← getProject st file

  let overrides := ps.overrides.insert file text
  let ps := { ps with overrides }
  stRef.set st

  let task : TaskM Error Val Global := buildEnv file
  let ctx : Incremental.Context := { config := ps.config, overrides := ps.overrides }

  match ← (Incremental.run ctx ps.engine task).toIO' with
  | .ok (_, engine') =>
      let ps' : ProjectState := { ps with engine := engine' }
      let root := ps.config.projectRoot.getD (file.parent.getD (FilePath.mk "."))
      stRef.modify fun st => setProject st root ps'
      publishDiagnostics hOut uri version? #[]
  | Except.error err =>
      let diag := mkDiagnostic text err
      publishDiagnostics hOut uri version? #[diag]

private def handleDidClose (hOut : IO.FS.Stream) (stRef : IO.Ref ServerState) (params? : Option Json.Structured) : IO Unit := do
  let some params := params?
    | throw (IO.userError "hover: missing params")
  let params ←
    match fromJson? (α := DidCloseTextDocumentParams) (toJson params) with
    | .ok ps => pure ps
    | .error e => throw (IO.userError s!"didClose: bad params: {e}")
  let uri := params.textDocument.uri
  if let some file ← uriToPath? uri then
    let st ← stRef.get
    let (st, ps) ← getProject st file
    let overrides := ps.overrides.erase file
    let ps := { ps with overrides }
    let root := ps.config.projectRoot.getD (file.parent.getD (FilePath.mk "."))
    let st := setProject st root ps
    stRef.set st
  publishDiagnostics hOut uri none #[]

private def handleHover
    (hOut : IO.FS.Stream)
    (id : RequestID)
    (stRef : IO.Ref ServerState)
    (params? : Option Json.Structured) : IO Unit := do
  let some params := params?
    | throw (IO.userError "hover: missing params")
  let params ←
    match fromJson? (α := HoverParams) (toJson params) with
    | .ok ps => pure ps
    | .error e => throw (IO.userError s!"hover: bad params: {e}")

  let uri := params.textDocument.uri
  let lspPos := params.position

  let some file ← uriToPath? uri
    | hOut.writeLspMessage <| Message.response id Json.null

  let st ← stRef.get
  let (st, ps) ← getProject st file
  stRef.set st

  let text := ps.overrides.getD file (← IO.FS.readFile file)
  let fileMap := Lean.FileMap.ofString text
  let bytePos := fileMap.lspPosToUtf8Pos lspPos

  let task : TaskM Error Val Global := buildEnv file
  let ctx : Incremental.Context := { config := ps.config, overrides := ps.overrides }

  match ← (Incremental.run ctx ps.engine task).toIO' with
  | .error _ =>
      hOut.writeLspMessage <| Message.response id Json.null
  | .ok (globalEnv, engine') =>
      let ps' : ProjectState := { ps with engine := engine' }
      let root := ps.config.projectRoot.getD (file.parent.getD (FilePath.mk "."))
      stRef.modify fun st => setProject st root ps'

      match ← Lsp.findHoverInGlobal ctx file.toString bytePos globalEnv with
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

partial def mainLoop (stdin stdout : IO.FS.Stream) (stRef : IO.Ref ServerState) : IO Unit := do
  while true do
    let msg ← stdin.readLspMessage
    match msg with
    | .request id method params? =>
        match method with
        | "initialize" =>
            try
              handleInitialize stdout id params?
            catch e =>
              stdout.writeLspMessage <|
                Message.responseError id ErrorCode.internalError s!"initialize failed: {e}" none
        | "shutdown" =>
            handleShutdown stdout id stRef
        | "textDocument/hover" =>
            try
              handleHover stdout id stRef params?
            catch e =>
              stdout.writeLspMessage <|
                Message.responseError id ErrorCode.internalError s!"hover failed: {e}" none
        | _ =>
            stdout.writeLspMessage <|
              Message.responseError id ErrorCode.methodNotFound s!"unknown method: {method}" none
    | .notification method params? =>
        match method with
        | "exit" => throw (IO.userError "exit")
        | "textDocument/didOpen" =>
            try handleDidOpen stdout stRef params? catch _ => pure ()
        | "textDocument/didChange" =>
            try handleDidChange stdout stRef params? catch _ => pure ()
        | "textDocument/didClose" =>
            try handleDidClose stdout stRef params? catch _ => pure ()
        | _ => pure ()
    | _ => pure ()

def main : IO UInt32 := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let stRef ← IO.mkRef { : ServerState}
  try
    mainLoop stdin stdout stRef
    pure 0
  catch e =>
    IO.println s!"fatal: {e}"
    pure 1
