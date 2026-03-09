#!/bin/bash

echo "inductive Nat where"
echo "  | zero"
echo "  | succ (n : Nat) : Nat"
echo
echo "inductive Eq.{u} (A : Type u) (a : A) : A → Type u where"
echo "  | refl : Eq.{u} A a a"
echo
for ((i = 0; i <= 1000; i++)); do
    echo "def n$i : Nat := Nat.zero"
    echo "example : n$i = Nat.zero := Eq.refl.{0} Nat Nat.zero"
done
