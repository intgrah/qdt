module

public import Incremental.Basic

@[expose] public section

namespace Incremental.Test.Fibonacci

abbrev config : BuildConfig where
  I := Empty
  V := nofun
  Q := Nat
  R _ := Nat
  rel := (· < ·)
  wf := Nat.lt_wfRel.wf

instance : Input config Unit where
  get := nofun
  set := nofun
  get_set_self := nofun
  get_set_other := nofun

instance : Hashable Empty := ⟨nofun⟩

def tasks : Tasks config
  | 0 => pure 0
  | 1 => pure 1
  | n + 2 => do
    let a ← fetch (n + 1) (by omega)
    let b ← fetch n (by omega)
    return a + b

end Incremental.Test.Fibonacci
