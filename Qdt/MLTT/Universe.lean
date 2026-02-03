import Lean.Data.Name

namespace Qdt

open Lean (Name)

inductive Universe where
  | level : Name → Universe
  | zero : Universe
  | succ : Universe → Universe
  | max : Universe → Universe → Universe
deriving Inhabited, Hashable, DecidableEq

namespace Universe

instance {n} : OfNat Universe n where
  ofNat := n.repeat .succ .zero

private def parenIf (p : Bool) : Std.Format → Std.Format :=
  if p then .paren else id

protected def reprPrec (u : Universe) (prec : Nat) : Std.Format :=
  match u with
  | .zero => "0"
  | .level n => toString n
  | .succ u' =>
    let rec countSuccs (acc : Nat) : Universe → Nat × Std.Format
      | .succ u'' => countSuccs (acc + 1) u''
      | .zero => (acc + 1, repr (acc + 1))
      | base => (acc + 1, parenIf (prec > 10) (base.reprPrec 66 ++ " + " ++ repr (acc + 1)))
    (countSuccs 0 u').snd
  | .max u' v' =>
    parenIf (prec > 10) ("max " ++ u'.reprPrec 11 ++ " " ++ v'.reprPrec 11)

instance : Repr Universe where
  reprPrec := Universe.reprPrec

instance : ToString Universe where
  toString u := (repr u).pretty

#guard toString (Universe.level `u |>.succ.succ.succ.succ) == "u + 4"

/- This code is copied from Lean 4 `src/Lean/Level.lean` -/

private def addOffset (u : Universe) : Nat → Universe
  | 0 => u
  | n + 1 => addOffset u.succ n

private def getOffset : Universe → Nat
  | .succ u => getOffset u + 1
  | _ => 0

private def getLevelOffset : Universe → Universe
  | .succ u => getLevelOffset u
  | u => u

private def ctorToNat : Universe → Nat
  | .zero   => 0
  | .level _ => 1
  | .succ _ => 2
  | .max _ _ => 3

private def normLtAux : Universe → Nat → Universe → Nat → Bool
  | .succ l₁, k₁, l₂, k₂ => normLtAux l₁ (k₁+1) l₂ k₂
  | l₁, k₁, .succ l₂, k₂ => normLtAux l₁ k₁ l₂ (k₂+1)
  | l₁@(.max l₁₁ l₁₂), k₁, l₂@(.max l₂₁ l₂₂), k₂ =>
    if l₁ == l₂ then k₁ < k₂
    else if l₁₁ != l₂₁ then normLtAux l₁₁ 0 l₂₁ 0
    else normLtAux l₁₂ 0 l₂₂ 0
  | .level n₁, k₁, .level n₂, k₂ => if n₁ == n₂ then k₁ < k₂ else Name.lt n₁ n₂
  | l₁, k₁, l₂, k₂ => if l₁ == l₂ then k₁ < k₂ else ctorToNat l₁ < ctorToNat l₂

private def normLt (l₁ l₂ : Universe) : Bool :=
  normLtAux l₁ 0 l₂ 0

@[specialize] private partial def getMaxArgsAux (normalise : Universe → Universe)
    : Universe → Bool → Array Universe → Array Universe
  | .max l₁ l₂, alreadyNorm, lvls =>
      lvls
      |> getMaxArgsAux normalise l₁ alreadyNorm
      |> getMaxArgsAux normalise l₂ alreadyNorm
  | l, false, lvls  => getMaxArgsAux normalise (normalise l) true lvls
  | l, true,  lvls  => lvls.push l

private def accMax (result : Universe) (prev : Universe) (offset : Nat) : Universe :=
  if result = .zero then addOffset prev offset
  else .max result (addOffset prev offset)

private def mkMaxAux (lvls : Array Universe) (extraK : Nat) (i : Nat)
    (prev : Universe) (prevK : Nat) (result : Universe) : Universe :=
  if h : i < lvls.size then
    let lvl := lvls[i]
    let curr := getLevelOffset lvl
    let currK := getOffset lvl
    if curr = prev then
      mkMaxAux lvls extraK (i+1) curr currK result
    else
      mkMaxAux lvls extraK (i+1) curr currK (accMax result prev (extraK + prevK))
  else
    accMax result prev (extraK + prevK)

private def skipExplicit (lvls : Array Universe) (i : Nat) : Nat :=
  if h : i < lvls.size then
    let lvl := lvls[i]
    if getLevelOffset lvl = .zero then skipExplicit lvls (i + 1) else i
  else
    i

private def isExplicitSubsumedAux (lvls : Array Universe) (maxExplicit : Nat) (i : Nat) : Bool :=
  if h : i < lvls.size then
    let lvl := lvls[i]
    if getOffset lvl ≥ maxExplicit then true
    else isExplicitSubsumedAux lvls maxExplicit (i + 1)
  else
    false

private def isExplicitSubsumed (lvls : Array Universe) (firstNonExplicit : Nat) : Bool :=
  if firstNonExplicit = 0 then false
  else
    let max := getOffset (lvls[firstNonExplicit - 1]!)
    isExplicitSubsumedAux lvls max firstNonExplicit

partial def normalise (l : Universe) : Universe :=
  let k := getOffset l
  let u := getLevelOffset l
  match u with
  | .max l₁ l₂ =>
      let lvls  := getMaxArgsAux normalise l₁ false #[]
      let lvls  := getMaxArgsAux normalise l₂ false lvls
      let lvls  := lvls.qsort normLt
      let first := skipExplicit lvls 0
      let i     := if isExplicitSubsumed lvls first then first else first - 1
      let lvl₁  := lvls[i]!
      let prev  := getLevelOffset lvl₁
      let prevK := getOffset lvl₁
      mkMaxAux lvls k (i + 1) prev prevK .zero
  | .zero      => addOffset .zero k
  | .level n   => addOffset (.level n) k
  | .succ u    => addOffset (normalise u) (k+1)

def levelNames : Universe → List Name
  | .level n => [n]
  | .zero => []
  | .succ u => u.levelNames
  | .max u v => u.levelNames ++ v.levelNames

/-- Fresh universe name of the form `u`, `u_1`, `u_2` -/
def freshName (existing : List Name) : Name :=
  if `u ∉ existing then `u
  else go 1 existing.length
where
  go (n fuel : Nat) : Name :=
    let name := Name.mkStr1 s!"u_{n}"
    match fuel with
    | 0 => name
    | fuel + 1 =>
      if name ∈ existing then go (n + 1) fuel
      else name

#guard freshName [] == `u
#guard freshName [`v] == `u
#guard freshName [`u] == `u_1
#guard freshName [`u, `u_1] == `u_2

def le (u v : Universe) : Bool :=
  go u.normalise v.normalise
where
  go (u v : Universe) : Bool :=
    u == v ||
    let k := fun () =>
      let u' := getLevelOffset u
      (getLevelOffset v == u' || .zero == u')
      && getOffset u ≤ getOffset v
    match u, v with
    | .zero, _ => true
    | .max u₁ u₂, v => go u₁ v && go u₂ v || k ()
    | u, .max v₁ v₂ => go u v₁ || go u v₂
    | .succ u, .succ v => go u v
    | _, _ => k ()
  termination_by (u, v)

section Tests

private abbrev u : Universe := .level `u
private abbrev v : Universe := .level `v

#guard le 0 0
#guard le 0 u
#guard le 0 1
#guard le u u
#guard le u u.succ
#guard le 1 2
#guard le 3 5
#guard !le u v
#guard !le u.succ v
#guard le (.max u v) (.max u v)
#guard le (.max u v) (.max v u)
#guard le (.max u v) (.max u.succ v)
#guard le (.max u v) (.max u v.succ)
#guard !le (.max u.succ v) (.max u v)
#guard !le (.max u v.succ) (.max u v)
#guard !le (.max u v.succ) (.max u.succ v)
#guard le (.max u v.succ) (.max u v.succ)
#guard le (.max u v.succ) (.max v.succ u)

end Tests

end Universe

end Qdt
