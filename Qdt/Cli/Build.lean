module

public import Cli.Extensions
public import Qdt.Cli
public import Qdt.Cli.Runner

@[expose] public section

open Cli

def Qdt.runBuild (parsed : Parsed) : IO UInt32 := do
  let cfg ← Qdt.parseConfig parsed
  Qdt.Cli.runBuild cfg

def Qdt.buildCmd : Cmd := `[Cli|
  build VIA Qdt.runBuild;
  "Elaborate QDT modules"

  FLAGS:
    r, root : String;              "Project root directory (default: cwd)"
    w, watch;                      "Enable watch mode"
    "build" : BuildSystem;         "Build system to use (default: shake-c)"

  ARGS:
    ...modules : String;           "Modules to check (dotted names; e.g. Std.Nat). Must not contain '/' or '.qdt'."

  EXTENSIONS:
    defaultValues! #[("build", "shake-c")]
]
