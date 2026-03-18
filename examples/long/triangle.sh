#!/bin/bash

echo "inductive Nat where"
echo "  | zero"
echo "  | succ (n : Nat) : Nat"
echo
echo "def Nat.add (m : Nat) : Nat → Nat :="
echo "  Nat.rec.{0} (fun (_ : Nat) => Nat) m (fun (_ : Nat) => Nat.succ)"
echo
echo "def n0 : Nat := Nat.zero"
for ((i = 1; i <= ${N:-100}; i++)); do
    printf "def n$i : Nat := "
    for ((j = 0; j < i; j++)); do
        if ((j > 0)); then
            printf " + "
        fi
        printf "n$j"
    done
    echo
done
