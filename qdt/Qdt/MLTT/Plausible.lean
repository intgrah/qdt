import Qdt.MLTT.Syntax

import Plausible

namespace Qdt

open Lean (Name)
open Plausible

instance {n} : Shrinkable (Idx (n + 1)) where
  shrink _ := []

instance {n} : Arbitrary (Idx (n + 1)) where
  arbitrary := SampleableExt.interpSample (Fin (n + 1))

instance : Shrinkable Universe where
  shrink _ := []

instance {n} : Shrinkable (Ty n) where
  shrink _ := []

instance {n} : Shrinkable (Tm n) where
  shrink _ := []

def Universe.sample : Nat → Gen Universe
  | 0 => return .zero
  | fuel + 1 => do
      match ← SampleableExt.interpSample (Fin 4) with
      | 0 => return .zero
      | 1 => return .level #[`u, `v, `w, `x][← SampleableExt.interpSample (Fin 4)]
      | 2 => return .succ (← sample fuel)
      | 3 => return .max (← sample fuel) (← sample fuel)

instance : Arbitrary Universe where
  arbitrary := Universe.sample 3

mutual
def Ty.sample (n : Nat) : Nat → Gen (Ty n)
  | 0 => return 𝑢 (← Universe.sample 2)
  | fuel + 1 => do
      match ← SampleableExt.interpSample (Fin 3) with
      | 0 => return .u (← Universe.sample 2)
      | 1 => return Ty.arrow (← Ty.sample n fuel) (← Ty.sample (n + 1) fuel)
      | 2 => return .el (← Tm.sample n fuel)

def Tm.sample (n : Nat) : Nat → Gen (Tm n)
  | 0 => do
      if h : 0 < n then
        let i ← SampleableExt.interpSample Nat
        return .var ⟨i % n, Nat.mod_lt i h⟩
      else return .const `x []
  | fuel + 1 => do
      match ← SampleableExt.interpSample (Fin 4) with
      | 0 =>
          if h : 0 < n then
            let i ← SampleableExt.interpSample Nat
            return .var ⟨i % n, Nat.mod_lt i h⟩
          else
            return .const `x []
      | 1 => return .const `c []
      | 2 => return .lam ⟨.anonymous, ← Ty.sample n fuel⟩ (← Tm.sample (n + 1) fuel)
      | 3 => return .app (← Tm.sample n fuel) (← Tm.sample n fuel)
end

instance {n} : Arbitrary (Ty n) where
  arbitrary := Ty.sample n 4

instance {n} : Arbitrary (Tm n) where
  arbitrary := Tm.sample n 4

end Qdt
