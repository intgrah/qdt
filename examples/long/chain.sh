#!/bin/sh

echo "inductive Nat where"
echo "  | zero"
echo "  | succ (n : Nat) : Nat"
echo
echo "inductive Eq.{u} (A : Type u) (a : A) : A → Type u where"
echo "  | refl : Eq.{u} A a a"
echo
echo "def f0 : Nat := 0"
i=1
while [ $i -le 1000 ]; do
    echo "def f$i : Nat := Nat.succ f$((i - 1))"
    i=$((i + 1))
done
