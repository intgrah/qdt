module

public import Lean.Data.Lsp.Communication

public import Qdt.Lsp.Hover
public import Qdt.Incremental.Rules
public import Lean.Data.Lsp.InitShutdown

@[expose] public section

namespace Qdt

open Std (HashMap)
open Lean JsonRpc Lsp
open System (FilePath)
open Incremental
open Incremental.Shake (Store Memo)
open Frontend (Cst Path SourceMap Span)

partial def utf8PosToCodepointPos (s : String) (bytePos : Nat) : Nat :=
  go 0 0
where
  go (cp : Nat) (bp : Nat) : Nat :=
    if bp ≥ bytePos then cp
    else if bp < s.utf8ByteSize then
      go (cp + 1) (String.Pos.Raw.next s ⟨bp⟩).byteIdx
    else cp

partial def codepointPosToUtf8Pos (s : String) (cpPos : Nat) : Nat :=
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
        let p ← IO.FS.realPath p
        pure (some p)
      catch _ =>
        pure (some p)

def findTomlUp (dir : FilePath) : Nat → IO (Option FilePath)
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

def normaliseConfig (cfg : Config) : IO Config := do
  let cwd ← IO.currentDir
  let root := cfg.projectRoot.getD cwd
  let root ← IO.FS.realPath root
  let sourceDirectories := cfg.sourceDirectories.map (root / ·)
  return {
    cfg with
    projectRoot := some root
    sourceDirectories
  }

structure ProjectState where
  config : Config
  store : Store Key Val

structure ServerState where
  projects : HashMap FilePath ProjectState := ∅
  shutdownRequested : Bool := false

def getProject (st : ServerState) (filepath : FilePath) : IO (ServerState × ProjectState) := do
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
      let ps : ProjectState := { config := cfg, store := {} }
      let st := { st with projects := st.projects.insert root ps }
      return (st, ps)

def setProject (st : ServerState) (root : FilePath) (ps : ProjectState) : ServerState :=
  { st with projects := st.projects.insert root ps }

def publishDiagnostics
    (hOut : IO.FS.Stream)
    (uri : DocumentUri)
    (version? : Option Int)
    (diags : Array Lsp.Diagnostic) : IO Unit := do
  let params : PublishDiagnosticsParams := { uri, version?, diagnostics := diags }
  match Json.toStructured? params with
  | Except.error e => throw (IO.userError s!"internal error: cannot encode diagnostics: {e}")
  | Except.ok s =>
      hOut.writeLspMessage <| Message.notification "textDocument/publishDiagnostics" (some s)

def elaborateFile (store : Store Key Val) (filepath : FilePath) :
    Option (Global × ElabInfo × SourceMap × Cst) := Id.run do
  let some cstMemo := store.cache.get? (Key.cst filepath) | return none
  let some smMemo := store.cache.get? (Key.astSourceMap filepath) | return none
  let some declMemo := store.cache.get? (Key.declarationIndex filepath) | return none
  let (cst, _) := cstMemo.value
  let (_, sourceMap, _) := smMemo.value
  let declIndex := declMemo.value
  let mut combinedInfo : ElabInfo := 1
  let mut combinedGlobal : Global := ∅

  for (name, _) in declIndex.toList do
    if let some infoMemo := store.cache.get? (Key.lookupInfo filepath name) then
      combinedInfo := combinedInfo * infoMemo.value
    if let some lookupMemo := store.cache.get? (Key.lookup filepath name) then
      if let some (constant, _) := lookupMemo.value then
        combinedGlobal := combinedGlobal.insert name constant

  let (_, _, astDiags) := smMemo.value
  let allDiags := astDiags ++ combinedInfo.diagnostics
  combinedInfo := { combinedInfo with diagnostics := allDiags }

  return some (combinedGlobal, combinedInfo, sourceMap, cst)

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

def handleInitialize (hOut : IO.FS.Stream) (id : RequestID) (params? : Option Json.Structured) : IO Unit := do
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

def handleShutdown (hOut : IO.FS.Stream) (id : RequestID) (stRef : IO.Ref ServerState) : IO Unit := do
  stRef.modify fun st => { st with shutdownRequested := true }
  hOut.writeLspMessage <| Message.response id Json.null

def sendFileProgress (hOut : IO.FS.Stream) (uri : DocumentUri) (ranges : Array Range) : IO Unit := do
  let processing := ranges.map fun r => Json.mkObj [("range", toJson r)]
  let params := Json.mkObj [
    ("textDocument", Json.mkObj [("uri", toJson uri)]),
    ("processing", toJson processing)
  ]
  match Json.toStructured? params with
  | .ok s => hOut.writeLspMessage <| Message.notification "$/lean/fileProgress" (some s)
  | .error _ => pure ()

def runElabTask (ps : ProjectState) (filepath : FilePath) :
    EIO Unit ((Global × ElabInfo × SourceMap × Cst) × Store Key Val) := do
  let store ← populateStore ps.config ps.store
  let store ← match Shake.build tasks (Key.checkFile filepath) store with
    | .ok (_, s) => pure s
    | .error _ => throw ()
  match elaborateFile store filepath with
  | some result => pure (result, store)
  | none => throw ()

def handleDidOpen (hOut : IO.FS.Stream) (stRef : IO.Ref ServerState) (params? : Option Json.Structured) : IO Unit := do
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
          : Lsp.Diagnostic
        }
      ]
      return

  let st ← stRef.get
  let (st, ps) ← getProject st file

  let memo : Memo Key Val (.text file) := { value := text, deps := ∅ }
  let store := { ps.store with cache := ps.store.cache.insert (.text file) memo }
  let ps := { ps with store }
  stRef.set st

  match ← (runElabTask ps file).toIO' with
  | .ok ((_, info, sourceMap, cst), store') =>
      let ps' : ProjectState := { ps with store := store' }
      let root := ps.config.projectRoot.getD (file.parent.getD (FilePath.mk "."))
      stRef.modify fun st => setProject st root ps'
      let diagnostics := buildDiagnostics text info sourceMap cst
      publishDiagnostics hOut uri version? diagnostics
      sendFileProgress hOut uri #[]
  | Except.error () =>
      publishDiagnostics hOut uri version? #[mkDiagnosticNoSpan (.msg "cycle detected")]
      sendFileProgress hOut uri #[]

def handleDidChange (hOut : IO.FS.Stream) (stRef : IO.Ref ServerState) (params? : Option Json.Structured) : IO Unit := do
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

  let memo : Memo Key Val (.text file) := { value := text, deps := ∅ }
  let store := { ps.store with cache := ps.store.cache.insert (.text file) memo }
  let ps := { ps with store }
  stRef.set st

  match ← (runElabTask ps file).toIO' with
  | .ok ((_, info, sourceMap, cst), store') =>
      let ps' : ProjectState := { ps with store := store' }
      let root := ps.config.projectRoot.getD (file.parent.getD (FilePath.mk "."))
      stRef.modify fun st => setProject st root ps'
      let diagnostics := buildDiagnostics text info sourceMap cst
      publishDiagnostics hOut uri version? diagnostics
      sendFileProgress hOut uri #[]
  | Except.error () =>
      publishDiagnostics hOut uri version? #[mkDiagnosticNoSpan (.msg "cycle detected")]
      sendFileProgress hOut uri #[]

def handleDidClose (hOut : IO.FS.Stream) (stRef : IO.Ref ServerState) (params? : Option Json.Structured) : IO Unit := do
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

    let cache := ps.store.cache.erase (.text file)
    let store := { ps.store with cache }

    let ps := { ps with store }
    let root := ps.config.projectRoot.getD (file.parent.getD (FilePath.mk "."))
    let st := setProject st root ps
    stRef.set st
  publishDiagnostics hOut uri none #[]

def handleHover
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

  let text ←
    match ps.store.cache.get? (.text file) with
    | some memo => pure memo.value
    | none => IO.FS.readFile file

  let fileMap := Lean.FileMap.ofString text
  let bytePos := fileMap.lspPosToUtf8Pos lspPos
  let codepointPos := utf8PosToCodepointPos text bytePos.byteIdx

  match ← (runElabTask ps file).toIO' with
  | .error () =>
      hOut.writeLspMessage <| Message.response id Json.null
  | .ok ((_, info, sourceMap, cst), store') =>
      let ps' : ProjectState := { ps with store := store' }
      let root := ps.config.projectRoot.getD (file.parent.getD (FilePath.mk "."))
      stRef.modify fun st => setProject st root ps'

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
          hOut.writeLspMessage <| Message.response id Json.null
      | some (cstPath, _, hover) =>
          let span := cst.spanAtPath cstPath |>.getD ⟨0, 0⟩
          let content := Lsp.formatHover hover
          let range := mkRange text span
          let markupContent : MarkupContent := {
            kind := MarkupKind.markdown
            value := s!"```qdt\n{content}\n```"
          }
          let hover : Hover := {
            contents := markupContent
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

end Qdt

open Qdt in
def main : IO UInt32 := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let stRef ← IO.mkRef ({ : ServerState} : ServerState)
  try
    mainLoop stdin stdout stRef
    pure 0
  catch e =>
    IO.println s!"fatal: {e}"
    pure 1
