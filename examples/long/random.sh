#!/bin/bash

echo "inductive Nat where"
echo "  | zero"
echo "  | succ (n : Nat) : Nat"
echo
echo "inductive Eq.{u} (A : Type u) (a : A) : A → Type u where"
echo "  | refl : Eq.{u} A a a"
echo
echo "def n0 : Nat := Nat.zero"
for ((i = 1; i <= ${N:-5000}; i++)); do
    echo "def n$i : Nat := Nat.succ n$((RANDOM % i))"
done
