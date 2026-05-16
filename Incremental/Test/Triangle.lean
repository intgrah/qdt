module

public import Incremental.Basic

@[expose] public section

namespace Incremental.Test.Triangle

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
  | n + 1 => do
    let prev ← fetch n (by omega)
    return prev + (n + 1)

end Incremental.Test.Triangle
