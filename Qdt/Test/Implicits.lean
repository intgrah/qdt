import Qdt.Test

open Qdt

#pass (
  inductive Nat where
    | zero
    | succ (n : Nat)

  inductive List.{u} (α : Type u) : Type u where
    | nil
    | cons (head : α) (tail : List α)

  def singleton.{u} (α : Type u) (x : α) : List α := List.cons x List.nil

  example : List Nat := List.cons 0 (List.cons 1 List.nil)
)

#pass (
  inductive List.{u} (α : Type u) : Type u where
    | nil
    | cons (head : α) (tail : List α)

  def singleton.{u} (α : Type u) (x : α) : List α :=
    @List.cons α x (@List.nil α)
)

#pass (
  inductive Nat where
    | zero
    | succ (n : Nat)

  inductive Eq.{u} {α : Type u} : α → α → Type u where
    | refl (a : α) : Eq a a

  def rfl.{u} {α : Type u} {a : α} : a = a := Eq.refl a

  example : (0 : Nat) = 0 := rfl
)

#pass (
  inductive Eq.{u} {α : Type u} : α → α → Type u where
    | refl (a : α) : Eq a a

  def reflEx.{u} (α : Type u) (a : α) : a = a := Eq.refl _
)

#pass (
  inductive Nat where
    | zero
    | succ (n : Nat)

  inductive Option.{u} (α : Type u) : Type u where
    | none
    | some (value : α)

  example : Option Nat := Option.none

  example : Option Nat := Option.some 5
)

#pass (
  inductive Nat where
    | zero
    | succ (n : Nat)

  inductive List.{u} (α : Type u) : Type u where
    | nil
    | cons (head : α) (tail : List α)

  def length.{u} (α : Type u) (xs : List α) : Nat :=
    @List.rec α (fun _ => Nat) 0 (fun _ _ acc => Nat.succ acc) xs
)

#pass (
  inductive Nat where
    | zero
    | succ (n : Nat)

  def id.{u} {α : Type u} (x : α) : α := x

  example : Nat := id 0

  example : Nat := @id Nat 0
)

#fail (
  inductive Option.{u} (α : Type u) : Type u where
    | none
    | some (value : α)

  def bad := Option.none
) with .unsolvedMetavariable ..

#pass (
  inductive Nat where
    | zero
    | succ (n : Nat)

  inductive List.{u} (α : Type u) : Type u where
    | nil
    | cons (head : α) (tail : List α)

  example : List Nat := List.cons Nat.zero List.nil

  example : List Nat := @List.cons Nat Nat.zero (@List.nil Nat)

  def length.{u} (α : Type u) (xs : List α) : Nat :=
    List.rec Nat.zero (fun h t acc => Nat.succ acc) xs

  def length'.{u} (α : Type u) (xs : List α) : Nat :=
    @List.rec α (fun _ => Nat) Nat.zero (fun h t acc => Nat.succ acc) xs
)
