#!/bin/bash

echo "inductive Nat where"
echo "  | zero"
echo "  | succ (n : Nat) : Nat"
echo
echo "inductive Eq.{u} (A : Type u) (a : A) : A → Type u where"
echo "  | refl : Eq.{u} A a a"
echo
for ((i = 0; i <= 1000; i++)); do
    echo "def f$i : Nat := 1"
    echo "example : f$i = 1 := Eq.refl.{0} Nat 1"
done
