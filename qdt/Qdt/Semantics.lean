import Qdt.MLTT.Syntax

namespace Qdt

open Lean (Name)

/-- de Bruijn levels -/
def Lvl n := Fin n
deriving Repr, BEq

mutual

inductive VTy : Nat → Type
  | u {n} : VTy n
  | pi {n} : VParam n → ClosTy n → VTy n
  | el {n} : Neutral n → VTy n
deriving Repr

inductive VTm : Nat → Type
  | neutral {n} : Neutral n → VTm n
  | lam {n} : VParam n → ClosTm n → VTm n
  | piHat {n} : Name → VTm n → ClosTm n → VTm n
deriving Repr

inductive Neutral : Nat → Type
  | mk {n} : Head n → Spine n → Neutral n
deriving Repr

inductive Head : Nat → Type
  | var {n} : Lvl n → Head n
  | const {n} : Name → Head n
deriving Repr

inductive Spine : Nat → Type
  | nil {n} : Spine n
  | app {n} : Spine n → VTm n → Spine n
  | proj {n} : Spine n → Nat → Spine n
deriving Repr

/-- Type closures -/
inductive ClosTy : Nat → Type
  | mk {n m} : Env n m → Ty (m + 1) → ClosTy n
deriving Repr

/-- Term closures -/
inductive ClosTm : Nat → Type
  | mk {n m} : Env n m → Tm (m + 1) → ClosTm n
deriving Repr

/-- Environments -/
inductive Env : Nat → Nat → Type
  | nil {n} : Env n 0
  | cons {n m} : VTm n → Env n m → Env n (m + 1)
deriving Repr

inductive VParam : Nat → Type
  | mk {n} (name : Name) (ty : VTy n) : VParam n
deriving Repr

end

def VTm.var {n} (i : Lvl n) : VTm n := .neutral ⟨.var i, .nil⟩
def VTm.varAt (n : Nat) {m} (h : n < m := by omega) : VTm m := .neutral ⟨.var ⟨n, h⟩, .nil⟩
def VTm.const {n} (name : Name) : VTm n := .neutral ⟨.const name, .nil⟩

def Neutral.head {n} : Neutral n → Head n | ⟨h, _⟩ => h
def Neutral.spine {n} : Neutral n → Spine n | ⟨_, sp⟩ => sp
def Neutral.app {n} : Neutral n → VTm n → Neutral n | ⟨h, sp⟩, a => ⟨h, sp.app a⟩
def Neutral.proj {n} : Neutral n → Nat → Neutral n | ⟨h, sp⟩, i => ⟨h, sp.proj i⟩

@[match_pattern]
def Head.apps {n} (h : Head n) (args : List (VTm n)) : Neutral n :=
  ⟨h, args.foldl Spine.app Spine.nil⟩

/--
Convert a spine of applications into a list of values.
Returns none if the spine contains projections.
-/
def Spine.toAppList {n} (sp : Spine n) : Option (List (VTm n)) :=
  let rec go : Spine n → Option (List (VTm n))
    | .nil => some []
    | .app sp t => List.cons t <$> go sp
    | .proj _ _ => none
  List.reverse <$> go sp

/-- Sanity check -/
example {n} (a b : VTm n) :
  (Spine.nil.app a |>.app b |>.toAppList) = some [a, b] := rfl

def Env.get {n c} : Idx c → Env n c → VTm n
  | i, .nil => nomatch i
  | ⟨0, _⟩, .cons t _ => t
  | ⟨k + 1, hk⟩, .cons _ rest => rest.get ⟨k, Nat.lt_of_succ_lt_succ hk⟩

def Env.ofList {n} : (xs : List (VTm n)) → Env n xs.length
  | [] => .nil
  | x :: xs => .cons x (ofList xs)

section Weakening

/-!
Since castLE is an irrelevant function (since proofs are erased at runtime),
we use unsafe casts to implement the weakenings with no runtime overhead.
-/

variable {n m : Nat}

private unsafe def VTy.weaken_impl (_ : n ≤ m) : VTy n → VTy m := unsafeCast
private unsafe def VTm.weaken_impl (_ : n ≤ m) : VTm n → VTm m := unsafeCast
private unsafe def Neutral.weaken_impl (_ : n ≤ m) : Neutral n → Neutral m := unsafeCast
private unsafe def Head.weaken_impl (_ : n ≤ m) : Head n → Head m := unsafeCast
private unsafe def Spine.weaken_impl (_ : n ≤ m) : Spine n → Spine m := unsafeCast
private unsafe def ClosTy.weaken_impl (_ : n ≤ m) : ClosTy n → ClosTy m := unsafeCast
private unsafe def ClosTm.weaken_impl (_ : n ≤ m) : ClosTm n → ClosTm m := unsafeCast
private unsafe def Env.weaken_impl {c} (_ : n ≤ m) : Env n c → Env m c := unsafeCast

mutual

@[implemented_by VTy.weaken_impl]
private def VTy.weaken' (h : n ≤ m) : VTy n → VTy m
  | .u => .u
  | .pi ⟨x, dom⟩ codom => .pi ⟨x, dom.weaken' h⟩ (codom.weaken' h)
  | .el ne => .el (ne.weaken' h)

@[implemented_by VTm.weaken_impl]
private def VTm.weaken' (h : n ≤ m) : VTm n → VTm m
  | .neutral ne => .neutral (ne.weaken' h)
  | .lam ⟨x, ty⟩ body => .lam ⟨x, ty.weaken' h⟩ (body.weaken' h)
  | .piHat name dom codom => .piHat name (dom.weaken' h) (codom.weaken' h)

@[implemented_by Head.weaken_impl]
private def Head.weaken' (h : n ≤ m) : Head n → Head m
  | .var lvl => .var (lvl.castLE h)
  | .const name => .const name

@[implemented_by Neutral.weaken_impl]
private def Neutral.weaken' (h : n ≤ m) : Neutral n → Neutral m
  | ⟨head, spine⟩ => ⟨head.weaken' h, spine.weaken' h⟩

@[implemented_by Spine.weaken_impl]
private def Spine.weaken' (h : n ≤ m) : Spine n → Spine m
  | .nil => .nil
  | .app sp t => .app (sp.weaken' h) (t.weaken' h)
  | .proj sp i => .proj (sp.weaken' h) i

@[implemented_by ClosTy.weaken_impl]
private def ClosTy.weaken' (h : n ≤ m) : ClosTy n → ClosTy m
  | ⟨env, ty⟩ => ⟨env.weaken' h, ty⟩

@[implemented_by ClosTm.weaken_impl]
private def ClosTm.weaken' (h : n ≤ m) : ClosTm n → ClosTm m
  | ⟨env, tm⟩ => ⟨env.weaken' h, tm⟩

@[implemented_by Env.weaken_impl]
private def Env.weaken' {c} (h : n ≤ m) : Env n c → Env m c
  | .nil => .nil
  | .cons t rest => .cons (t.weaken' h) (rest.weaken' h)

end

/-!
Attempt to synthesise the proof automatically by the omega tactic.
-/

def VTy.weaken (h : n ≤ m := by omega) : VTy n → VTy m := VTy.weaken' h
def VTm.weaken (h : n ≤ m := by omega) : VTm n → VTm m := VTm.weaken' h
def Env.weaken {c} (h : n ≤ m := by omega) : Env n c → Env m c := Env.weaken' h

end Weakening

end Qdt
