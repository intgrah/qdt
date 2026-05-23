module

public import Cli.Basic
public import Qdt.Cli.Build
public import Qdt.Cli.Fmt
public import Qdt.Cli.Lsp

open Cli

def Qdt.printHelp (p : Parsed) : IO UInt32 := do
  p.printHelp
  return 0

def Qdt.cmd : Cmd := `[Cli|
  qdt VIA Qdt.printHelp;
  "Query-based Dependent Type elaborator"

  SUBCOMMANDS:
    Qdt.buildCmd;
    Qdt.fmtCmd;
    Qdt.lspCmd
]

public def main : List String → IO UInt32 :=
  Qdt.cmd.validate
