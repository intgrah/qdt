import Qdt.Parser
import Qdt.Elab

open Qdt

def main (args : List String) : IO Unit := do
  match args with
  | [] =>
      IO.eprintln "Usage: qdt <file>"
      IO.Process.exit 1
  | file :: _ =>
      let contents ← IO.FS.readFile file
      match parseString contents with
      | .error msg =>
          IO.eprintln s!"Parse error: {msg}"
          IO.Process.exit 1
      | .ok program =>
          match elabProgram program with
          | .error (.msg msg) =>
              IO.eprintln s!"Elaboration error: {msg}"
              IO.Process.exit 1
          | .ok defs =>
              for (name, term, ty) in defs do
                IO.println s!"def {name} : {repr ty} :=\n{repr term}"
                IO.println ""
