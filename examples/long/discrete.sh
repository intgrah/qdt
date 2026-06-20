#!/bin/bash

echo "inductive Nat where"
echo "  | zero"
echo "  | succ (n : Nat) : Nat"
echo
echo "inductive Eq.{u} {α : Type u} : α → α → Type u where"
echo "  | refl (a : α) : Eq a a"
echo
for ((i = 1; i <= ${N:-1000}; i++)); do
    echo "def n$i : Nat := Nat.zero"
    echo "example : n$i = Nat.zero := Eq.refl Nat.zero"
done
