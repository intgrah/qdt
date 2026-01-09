import Qdt.MLTT.Syntax

import Plausible

namespace Qdt

open Lean (Name)
open Plausible

instance {n} : Shrinkable (Idx (n + 1)) where
  shrink _ := []

instance {n} : Arbitrary (Idx (n + 1)) where
  arbitrary := SampleableExt.interpSample (Fin (n + 1))

instance {n} : Shrinkable (Ty n) where
  shrink _ := []

instance {n} : Shrinkable (Tm n) where
  shrink _ := []

mutual
partial def Ty.sample (n : Nat) (fuel : Nat) : Gen (Ty n) := do
  if fuel = 0 then return 𝑢
  else
    let choice ← SampleableExt.interpSample (Fin 3)
    match choice.val with
    | 0 => return 𝑢
    | 1 =>
      let a ← Ty.sample n (fuel - 1)
      let b ← Ty.sample (n + 1) (fuel - 1)
      return a.arrow b
    | _ =>
      let t ← Tm.sample n (fuel - 1)
      return .el t

partial def Tm.sample (n : Nat) (fuel : Nat) : Gen (Tm n) := do
  if fuel = 0 then
    if h : 0 < n then
      let i ← SampleableExt.interpSample Nat
      return .var ⟨i % n, Nat.mod_lt i h⟩
    else
      return .const `x
  else
    let choice ← SampleableExt.interpSample (Fin 4)
    match choice.val with
    | 0 =>
      if h : 0 < n then
        let i ← SampleableExt.interpSample Nat
        return .var ⟨i % n, Nat.mod_lt i h⟩
      else
        return .const `x
    | 1 => return .const `c
    | 2 =>
      let a ← Ty.sample n (fuel - 1)
      let body ← Tm.sample (n + 1) (fuel - 1)
      return .lam ⟨.anonymous, a⟩ body
    | _ =>
      let f ← Tm.sample n (fuel - 1)
      let a ← Tm.sample n (fuel - 1)
      return .app f a
end

instance {n} : Arbitrary (Ty n) where
  arbitrary := Ty.sample n 4

instance {n} : Arbitrary (Tm n) where
  arbitrary := Tm.sample n 4

end Qdt
