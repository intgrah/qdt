module

public import Qdt.Cli.Runner.Id
public import Qdt.Cli.Runner.Trace

@[expose] public section

namespace Qdt.Cli

open Incremental

def runBuild (cfg : Config) : IO UInt32 :=
  match cfg.buildSystem with
  | .busy => Runner.runId cfg (Busy config Input (inferInstance : Monad Id) tasks)
  | .lessBusy => Runner.runId cfg (LessBusy config Input tasks)
  | .salsa => Runner.runId cfg (Salsa config Input tasks)
  | .salsaC => Runner.runId cfg (SalsaC config Input tasks)
  | .shake => Runner.runId cfg
      (Shake config Input (fun _ => Hashable.toEmbedding) (fun _ => Hashable.toEmbedding) tasks)
  | .shakeC => Runner.runId cfg (ShakeC config Input tasks)
  | .shakeTrace => Runner.runTrace cfg

end Qdt.Cli
