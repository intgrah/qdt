import Qdt.Tele
import Qdt.MLTT.Universe
import Qdt.Frontend.Source

namespace Qdt

open Lean (Name)
open Frontend (Src)

/-- de Bruijn indices -/
def Idx n := Fin n
deriving Repr, Hashable, DecidableEq, BEq

/-- Allow natural number literals to be used as de Bruijn indices -/
instance {n} [NeZero n] {i} : OfNat (Idx n) i where
  ofNat := Fin.ofNat n i

mutual

/-- Types -/
inductive Ty : Nat → Type
  | u {n} : Src → Universe → Ty n
  | pi {n} : Src → Param n → Ty (n + 1) → Ty n
  /-- If Γ ⊢ t : 𝑢 i, then Γ ⊢ El(t) type -/
  | el {n} : Src → Tm n → Ty n
deriving Repr

/-- Terms -/
inductive Tm : Nat → Type
  | u' {n} : Src → Universe → Tm n
  | var {n} : Src → Idx n → Tm n
  | const {n} : Src → Name → List Universe → Tm n
  | lam {n} : Src → Param n → Tm (n + 1) → Tm n
  | app {n} : Src → Tm n → Tm n → Tm n
  | pi' {n} : Src → Param' n → Tm (n + 1) → Tm n
  | proj {n} : Src → Nat → Tm n → Tm n
  | letE {n} : Src → Name → Ty n → Tm n → Tm (n + 1) → Tm n
deriving Repr

@[pp_using_anonymous_constructor]
inductive Param : Nat → Type
  | mk {n} (src : Src) (name : Name) (ty : Ty n) : Param n
deriving Repr

@[pp_using_anonymous_constructor]
inductive Param' : Nat → Type
  | mk {n} (src : Src) (name : Name) (tm : Tm n) : Param' n
deriving Repr

end

def Ctx := Tele Param

notation "𝑢" => Ty.u none

abbrev Ty.arrow {n} (ty : Ty n) := Ty.pi none ⟨none, .anonymous, ty⟩

/-- Replace the source span of a term only if target has no span -/
def Tm.withSrc {n} (newSrc : Src) : Tm n → Tm n
  | .u' oldSrc u => .u' (oldSrc <|> newSrc) u
  | .var oldSrc i => .var (oldSrc <|> newSrc) i
  | .const oldSrc name us => .const (oldSrc <|> newSrc) name us
  | .lam oldSrc p body => .lam (oldSrc <|> newSrc) p body
  | .app oldSrc f a => .app (oldSrc <|> newSrc) f a
  | .pi' oldSrc ⟨pSrc, x, a⟩ b => .pi' (oldSrc <|> newSrc) ⟨pSrc, x, a⟩ b
  | .proj oldSrc i t => .proj (oldSrc <|> newSrc) i t
  | .letE oldSrc x ty val body => .letE (oldSrc <|> newSrc) x ty val body

@[match_pattern]
def Tm.apps {n} : Tm n → List (Tm n) → Tm n :=
  List.foldl (Tm.app none)

/- Point free! Point free! -/
def Ty.pis {a b} : Ctx a b → Ty b → Ty a
  | .nil => id
  | .snoc bs param => pis bs ∘ pi none param

def Ty.getResultUniverse? {n} : Ty n → Option Universe
  | .u _ univ => some univ
  | .pi _ _ cod => cod.getResultUniverse?
  | .el _ _ => none

def Tm.lams {a b} : Ctx a b → Tm b → Tm a
  | .nil => id
  | .snoc bs param => lams bs ∘ lam none param

private def lookup (subst : List (Name × Universe)) (n : Name) : Universe :=
  match subst.find? (·.fst == n) with
  | some (_, u) => u
  | none => .level n

mutual

def Universe.subst (subst : List (Name × Universe)) : Universe → Universe
  | .level n => lookup subst n
  | .zero => .zero
  | .succ u => .succ (u.subst subst)
  | .max u v => .max (u.subst subst) (v.subst subst)

def Ty.substLevels {n} (subst : List (Name × Universe)) : Ty n → Ty n
  | .u src u => .u src (u.subst subst)
  | .pi src ⟨psrc, name, ty⟩ b => .pi src ⟨psrc, name, ty.substLevels subst⟩ (b.substLevels subst)
  | .el src t => .el src (t.substLevels subst)

def Tm.substLevels {n} (subst : List (Name × Universe)) : Tm n → Tm n
  | .u' src u => .u' src (u.subst subst)
  | .var src i => .var src i
  | .const src c us => .const src c (us.map (·.subst subst))
  | .lam src ⟨psrc, name, ty⟩ b => .lam src ⟨psrc, name, ty.substLevels subst⟩ (b.substLevels subst)
  | .app src f a => .app src (f.substLevels subst) (a.substLevels subst)
  | .pi' src ⟨pSrc, name, a⟩ b => .pi' src ⟨pSrc, name, a.substLevels subst⟩ (b.substLevels subst)
  | .proj src i t => .proj src i (t.substLevels subst)
  | .letE src name ty rhs body =>
      .letE src name (ty.substLevels subst) (rhs.substLevels subst) (body.substLevels subst)

def Param.substLevels {n} (subst : List (Name × Universe)) : Param n → Param n
  | ⟨src, name, ty⟩ => ⟨src, name, ty.substLevels subst⟩

end

mutual

def Ty.levelNames {n} : Ty n → List Name
  | .u _ u => u.levelNames
  | .pi _ ⟨_, _, ty⟩ b => ty.levelNames ++ b.levelNames
  | .el _ t => t.levelNames

def Tm.levelNames {n} : Tm n → List Name
  | .u' _ u => u.levelNames
  | .var _ _ => []
  | .const _ _ us => us.flatMap Universe.levelNames
  | .lam _ ⟨_, _, ty⟩ b => ty.levelNames ++ b.levelNames
  | .app _ f a => f.levelNames ++ a.levelNames
  | .pi' _ ⟨_, _, a⟩ b => a.levelNames ++ b.levelNames
  | .proj _ _ t => t.levelNames
  | .letE _ _ ty rhs body => ty.levelNames ++ rhs.levelNames ++ body.levelNames

def Param.levelNames {n} : Param n → List Name
  | ⟨_, _, ty⟩ => ty.levelNames

end

/-!
## Hashable instances

Since mutual inductives cannot derive Hashable automatically, we define them manually.
Source info (`Src`) hashes to 0 so it doesn't affect semantic equality.
-/

mutual

def Ty.hash {n} : Ty n → UInt64
  | .u src u => mixHash 1 (mixHash (hash src) (hash u))
  | .pi src p b => mixHash 2 (mixHash (hash src) (mixHash p.hash b.hash))
  | .el src t => mixHash 3 (mixHash (hash src) t.hash)

def Tm.hash {n} : Tm n → UInt64
  | .u' src u => mixHash 10 (mixHash (hash src) (hash u))
  | .var src i => mixHash 11 (mixHash (hash src) (hash i))
  | .const src name us => mixHash 12 (mixHash (hash src) (mixHash (hash name) (hash us)))
  | .lam src p body => mixHash 13 (mixHash (hash src) (mixHash p.hash body.hash))
  | .app src f a => mixHash 14 (mixHash (hash src) (mixHash f.hash a.hash))
  | .pi' src ⟨pSrc, name, a⟩ b => mixHash 15 (mixHash (hash src) (mixHash (hash pSrc) (mixHash (hash name) (mixHash a.hash b.hash))))
  | .proj src i t => mixHash 16 (mixHash (hash src) (mixHash (hash i) t.hash))
  | .letE src name ty val body => mixHash 17 (mixHash (hash src) (mixHash (hash name) (mixHash ty.hash (mixHash val.hash body.hash))))

def Param.hash {n} : Param n → UInt64
  | ⟨src, name, ty⟩ => mixHash (hash src) (mixHash (hash name) ty.hash)

end

instance {n} : Hashable (Ty n) := ⟨Ty.hash⟩
instance {n} : Hashable (Tm n) := ⟨Tm.hash⟩
instance {n} : Hashable (Param n) := ⟨Param.hash⟩

end Qdt
