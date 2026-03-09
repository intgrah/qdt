#!/bin/bash

echo "inductive Nat where"
echo "  | zero"
echo "  | succ (n : Nat) : Nat"
echo
echo "inductive Eq.{u} (A : Type u) (a : A) : A → Type u where"
echo "  | refl : Eq.{u} A a a"
echo
echo "def f0 : Nat := 0"
for ((i = 1; i <= 5000; i++)); do
    echo "def f$i : Nat := Nat.succ f$((RANDOM % i))"
done
