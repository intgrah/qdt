module

public import Qdt.Cli.Runner.Id
public import Qdt.Cli.Runner.Trace
public import Incremental.Busy
public import Incremental.LessBusy
public import Incremental.Salsa
public import Incremental.SalsaC
public import Incremental.Shake.Standard
public import Incremental.Shake.C
public import Incremental.Shake.Rdeps

@[expose] public section

namespace Qdt.Cli

open Incremental

def runBuild (cfg : Config) : IO UInt32 :=
  match cfg.buildSystem with
  | .busy => Runner.runId cfg (Busy config Input tasks)
  | .lessBusy => Runner.runId cfg (LessBusy config Input tasks)
  | .salsa => Runner.runId cfg (Salsa config Input tasks)
  | .salsaC => Runner.runId cfg (SalsaC config Input tasks)
  | .shake => Runner.runId cfg
      (Shake config Input (fun _ => Hashable.toEmbedding) (fun _ => Hashable.toEmbedding) tasks)
  | .shakeC => Runner.runId cfg (ShakeC config Input tasks)
  | .shakeRdeps => Runner.runId cfg (ShakeRdeps config Input tasks)
  | .shakeTrace => Runner.runTrace cfg

end Qdt.Cli
