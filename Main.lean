module

public import Cli.Extensions
public import Qdt.Cli
public import Qdt.Cli.Runner

open Cli

def Qdt.cmd : Cmd := `[Cli|
  qdt VIA run;
  "Query-based Dependent Type elaborator"

  FLAGS:
    r, root : String;              "Project root directory (default: cwd)"
    w, watch;                      "Enable watch mode"
    "build" : BuildSystem;         "Build system to use (default: shake-c)"

  ARGS:
    ...modules : String;           "Modules to check"

  EXTENSIONS:
    defaultValues! #[("build", "shake-c")]
]
  where run (parsed : Parsed) : IO UInt32 := do
    let cfg ← parseConfig parsed
    Qdt.Cli.runBuild cfg

public def main : List String → IO UInt32 :=
  Qdt.cmd.validate
