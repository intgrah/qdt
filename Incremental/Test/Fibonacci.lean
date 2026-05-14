import Incremental.Basic

namespace Incremental.Test.Fibonacci

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
  | 1 => pure 1
  | n + 2 => do
    let a ← Incremental.fetch (n + 1) (by omega)
    let b ← Incremental.fetch n (by omega)
    return a + b

end Incremental.Test.Fibonacci
