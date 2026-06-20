import Qdt.Test

#pass (
  inductive Eq.{u} {α : Type u} : α → α → Type u where
    | refl (a : α) : Eq a a

  inductive Nat where
    | zero
    | succ (n : Nat)

  def Nat.add (m n : Nat) : Nat :=
    Nat.rec m (fun _ k => Nat.succ k) n

  def myLemma (n : Nat) : Nat.add n n = Nat.add n n :=
    let m := Nat.add n;
    Eq.refl (m n)
)
