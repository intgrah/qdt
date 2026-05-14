import Incremental.Basic

namespace Incremental.Test.Triangle

abbrev config : Incremental.BuildConfig where
  I := Empty
  V := nofun
  Q := Nat
  R _ := Nat
  rel := (· < ·)
  wf := Nat.lt_wfRel.wf

instance : Incremental.Input config Unit where
  get := nofun
  set := nofun
  get_set_self := nofun
  get_set_other := nofun

instance : Hashable Empty := ⟨nofun⟩

def tasks : Incremental.Tasks config
  | 0 => pure 0
  | n + 1 => do
    let prev ← Incremental.fetch n (by omega)
    return prev + (n + 1)

end Incremental.Test.Triangle
