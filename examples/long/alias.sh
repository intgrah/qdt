#!/bin/bash

echo "inductive Nat where"
echo "  | zero"
echo "  | succ (n : Nat) : Nat"
echo
echo "def n0 : Nat := Nat.zero"
for ((i = 1; i <= ${N:-1000}; i++)); do
    echo "def n$i : Nat := n$((i - 1))"
done
