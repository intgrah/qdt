import Qdt.Test

#pass (
  inductive Eq.{u} {α : Type u} : α → α → Type u where
    | refl (a : α) : Eq a a

  inductive Nat where
    | zero
    | succ (n : Nat)

  def chain (n : Nat) : (fun (x : Nat) => x) ((fun (y : Nat) => y) n) = n :=
    Eq.refl _
)
