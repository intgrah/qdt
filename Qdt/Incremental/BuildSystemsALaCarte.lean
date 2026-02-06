import Batteries.Control.AlternativeMonad
import Mathlib.Control.Monad.Writer

/-!
# Build Systems à la Carte

Lean port of code from the paper
-/

namespace BuildSystems

universe u

section Defs

variable (c : (Type u → Type u) → Type (u + 1)) (I IR Q : Type u) (R : Q → Type u)

structure Store where
  info : I
  values : ∀ q, R q

set_option checkBinderAnnotations false in
def Task (q : Q) := ∀ {f} [c f], (∀ q, f (R q)) → f (R q)
def Tasks := ∀ q, Option (Task c Q R q)
def Build := Tasks c Q R → Q → Store I Q R → Store I Q R

/-- MonadState σ m doesn't actually impose Monad m, so we extend it -/
class MonadStateM σ m extends MonadState σ m, Monad m
instance {σ} : MonadStateM σ (StateM σ) where

def Rebuilder := ∀ q, R q → Task c Q R q → Task (MonadStateM IR) Q R q
def Scheduler := Rebuilder c IR Q R → Build c I Q R

end Defs

def sprsh₁ : Tasks Applicative String fun _ => Nat
  | "B1" => some fun fetch => (· + ·) <$> fetch "A1" <*> fetch "A2"
  | "B2" => some fun fetch => (· * 2) <$> fetch "B1"
  | _ => none

section Busy

variable {Q : Type u} [DecidableEq Q] {R : Q → Type u}

unsafe def busy : Build Applicative PUnit Q R := fun tasks key store =>
  let rec fetch q : StateM (Store PUnit Q R) (R q) :=
    match tasks q with
    | none => return (← get).values q
    | some task => do
      let r ← task fetch
      modify (fun st => { st with values := fun x => if h : x = q then h ▸ r else st.values x })
      return r
  StateT.run (fetch key) store |>.snd

end Busy

def store : Store Unit String fun _ => Nat where
  info := ()
  values
    | "A1" => 10
    | _ => 20

unsafe def result := busy sprsh₁ "B2" store

/-- info: 30 -/
#guard_msgs in
#eval result.values "B1"
/-- info: 60 -/
#guard_msgs in
#eval result.values "B2"

variable {c : (Type u → Type u) → Type (u + 1)} {I Q : Type u} {R : Q → Type u}

#check Task Applicative
#check Task Monad
#check Task Functor
#check Task Alternative
#check Task AlternativeMonad
#check Task (MonadState I)

def sprsh₂ : Tasks Monad String (fun _ => Nat)
  | "B1" => some fun fetch => do
    let c1 ← fetch "C1"
    if c1 == 1 then fetch "B2" else fetch "A2"
  | "B2" => some fun fetch => do
    let c1 ← fetch "C1"
    if c1 == 1 then fetch "A1" else fetch "B1"
  | _ => none

def compute (q : Q) (task : Task Monad Q R q) (store : Store I Q R) : R q :=
  Id.run do task store.values

section Correctness

def Correctness
    (build : Build c I Q R)
    (tasks : Tasks c Q R)
    (q : Q)
    (store result : Store I Q R) :=
  result = build tasks q store

def Agree
    (tasks : Tasks c Q R)
    (result store : Store I Q R) :=
  ∀ q, tasks q = none → result.values q = store.values q

def Consistent
    (tasks : Tasks Monad Q R)
    (result : Store I Q R) :=
  ∀ q task, tasks q = some task →
  result.values q = compute q task result

end Correctness

def Const : Type u → Type u → Type u := Function.const (α := Type u) (Type u)

instance {α} [inst : Monoid α] : Applicative (Const α) where
  pure _ := inst.one
  seq f x := inst.mul f (x ())

instance {α} : Monoid (List α) where
  one := []
  mul := List.append
  one_mul := List.nil_append
  mul_one := List.append_nil
  mul_assoc := List.append_assoc

def dependencies {q} (task : Task Applicative Q R q) : List Q :=
  letI fetch : ∀ q, Const (List Q) (R q) := List.singleton
  task fetch

/-- info:
some ["A1", "A2"]
-/
#guard_msgs in
#eval (sprsh₁ "B1").map dependencies

/-- info:
some ["B1"]
-/
#guard_msgs in
#eval (sprsh₁ "B2").map dependencies

def track {m} [Monad m] {q} (task : Task Monad Q R q) (fetch : ∀ q, m (R q)) : m (R q × List (Σ q, R q)) :=
  let trackingFetch (q : Q) : WriterT (List (Σ q, R q)) m (R q) := do
    let r ← fetch q
    tell [⟨q, r⟩]
    return r
  WriterT.run (task trackingFetch)

def fetchIO (mock : String → Nat) (q : String) : IO Nat := do
  let r := mock q
  println! "{q}: {r}"
  return r

/-- info:
C1: 1
B2: 10
--- info:
some (10, [⟨"C1", 1⟩, ⟨"B2", 10⟩])
-/
#guard_msgs in
#eval (sprsh₂ "B1").mapM (track (q := "B1") · (fetchIO fun | "C1" => 1 | "B2" => 10 | _ => 0))

/-- info:
C1: 2
A2: 20
--- info:
some (20, [⟨"C1", 2⟩, ⟨"A2", 20⟩])
-/
#guard_msgs in
#eval (sprsh₂ "B1").mapM (track (q := "B1") · (fetchIO fun | "C1" => 2 | "A2" => 20 | _ => 0))

section Traces

variable (Q : Type) [DecidableEq Q] (R : Q → Type) (Hash : Type → Type) {m} [Monad m]

/-- 4.2.2 Verifying Traces -/
def VT := List (Σ q, Hash (R q) × List (Σ d, Hash (R d)))

def recordVT (q : Q) (h : Hash (R q)) (deps : List (Σ d, Hash (R d))) : VT Q R Hash → VT Q R Hash :=
  List.cons ⟨q, h, deps⟩

def verifyVT [∀ α, DecidableEq (Hash α)]
    (vt : VT Q R Hash) (key : Q) (h : Hash (R key)) (fetchHash : ∀ d, m (Hash (R d))) : m Bool := do
  let rec matchTrace : List (Σ q, Hash (R q) × List (Σ d, Hash (R d))) → m Bool
    | [] => return false
    | ⟨q, h', deps⟩ :: rest => do
      if heq : q = key then
        match heq with
        | rfl =>
          if h == h' then
            let depMatch : (Σ d, Hash (R d)) → m Bool := fun ⟨d, dh⟩ => do
              let currentDh ← fetchHash d
              return currentDh == dh
            if ← deps.allM depMatch then return true else matchTrace rest
          else
            matchTrace rest
      else
        matchTrace rest
  matchTrace vt

/-- 4.2.3 Constructive Traces -/
def CT := List (Σ q, R q × List (Σ d, Hash (R d)))

def recordCT (q : Q) (v : R q) (deps : List (Σ d, Hash (R d))) : CT Q R Hash → CT Q R Hash :=
  List.cons ⟨q, v, deps⟩

def constructCT [∀ α, DecidableEq (Hash α)]
    (ct : CT Q R Hash) (key : Q) (fetchHash : ∀ d, m (Hash (R d))) : m (List (R key)) := do
  let rec findMatches : List (Σ q, R q × List (Σ d, Hash (R d))) → m (List (R key))
    | [] => return []
    | ⟨q, val, deps⟩ :: rest => do
      let others ← findMatches rest
      if heq : q = key then
        match heq with
        | rfl =>
          let depMatch : (Σ d, Hash (R d)) → m Bool := fun ⟨d, dh⟩ => do
            let currentDh ← fetchHash d
            return currentDh == dh
          if ← deps.allM depMatch then return val :: others else return others
      else
        return others
  findMatches ct

end Traces

section Make

open Std (HashSet)

variable {Q : Type u} [DecidableEq Q] [Hashable Q] {R : Q → Type u}

abbrev Time := Nat

def MakeInfo (Q : Type u) := Time × List (Q × Time)

def liftStore {α : Type u} (x : StateM I α) : StateM (Store I Q R) α := do
  let s ← get
  let (a, info) := x.run s.info
  set { s with info }
  return a

def modTimeRebuilder : Rebuilder Applicative (MakeInfo Q) Q R :=
  fun q r task {f} [MonadStateM (MakeInfo Q) f] fetch => do
    let (now, modTimes) ← get
    let dirty : Bool :=
      match modTimes.lookup q with
      | none => true
      | some time => (dependencies task).any fun d =>
          match modTimes.lookup d with
          | none => false
          | some depTime => depTime > time
    if not dirty then
      return r
    else
      modify fun _ => (now + 1, (q, now) :: modTimes)
      task fetch

abbrev Graph (Q : Type u) := List (Q × List Q)

partial def reachable (adj : Q → List Q) (start : Q) : Graph Q :=
  let rec loop (visited : HashSet Q) (acc : Graph Q) : List Q → Graph Q
    | [] => acc
    | u :: stack =>
      if visited.contains u then
        loop visited acc stack
      else
        let neighbors := adj u
        let visited := visited.insert u
        loop visited ((u, neighbors) :: acc) (neighbors ++ stack)
  loop ∅ [] [start]

partial def topSort (g : Graph Q) : List Q :=
  let rec visit (n : Q) (visited : HashSet Q) (sorted : List Q) : HashSet Q × List Q :=
    if visited.contains n then
      (visited, sorted)
    else
      let visited := visited.insert n
      let neighbors := g.lookup n |>.getD []
      let (visited, sorted) := neighbors.foldl (fun (v, s) child => visit child v s) (visited, sorted)
      (visited, n :: sorted)
  g.foldl (fun (_, s) (n, _) => visit n ∅ s) (∅, []) |>.snd

def topological : Scheduler Applicative I I Q R :=
  fun rebuilder tasks target store =>
  let dep k : List Q := match tasks k with | none => [] | some t => dependencies t
  let order := topSort (reachable dep target)
  let build (q : Q) : StateM (Store I Q R) PUnit :=
    match tasks q with
    | none => return ⟨⟩
    | some task => do
      let store ← get
      let r := store.values q
      let newTask : Task (MonadStateM I) Q R q := rebuilder q r task
      let fetch k : StateM I (R k) := return store.values k
      let newValue ← liftStore (newTask fetch)
      modify fun s => { s with values := fun k => if h : k = q then h ▸ newValue else s.values k }
  StateT.run (order.forM build) store |>.snd

def make : Build Applicative (MakeInfo Q) Q R := topological modTimeRebuilder

end Make

end BuildSystems
