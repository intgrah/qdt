module

public import Qdt.Semantics
public import Qdt.Theory.Substitution.Basic

public section

namespace Qdt

open Lean (Name)

def Tm.getAppArgs {n : Nat} : Tm n → Tm n × List (Tm n) :=
  go []
where
  go {n : Nat} (spine : List (Tm n)) : Tm n → Tm n × List (Tm n)
    | .app f a => go (a :: spine) f
    | t => (t, spine)

def Ty.getTele {a : Nat} : Ty a → Σ b, Ctx a b × Ty b :=
  go Tele.nil
where
  go {a b : Nat}
      (acc : Ctx a b) :
      Ty b →
      Σ nb : Nat, Ctx a nb × Ty nb
    | .pi name bi ty b => go (acc.snoc (name, bi, ty)) b
    | t => ⟨b, acc, t⟩

unsafe def weaken_impl {n m : Nat} : List (VTm n) → (_ : n ≤ m) → List (VTm m) := unsafeCast

def weaken' {n m : Nat} (ts : List (VTm n)) (h : n ≤ m) : List (VTm m) :=
  ts.map (VTm.weaken h)

public def weaken {n m : Nat} (ts : List (VTm n)) (h : n ≤ m := by omega) : List (VTm m) := weaken' ts h

def Env.infer : {n : Nat} → Env n n
  | 0 => Env.nil
  | n + 1 => Env.infer.weaken.cons (VTm.varAt n)

mutual

def Tm.hasIndOcc {n : Nat} (ind : Name) : Tm n → Bool
  | .u' _ => false
  | .var _ => false
  | .const name _ => name == ind
  | .lam _ _ a b => a.hasIndOcc ind || b.hasIndOcc ind
  | .app a b => a.hasIndOcc ind || b.hasIndOcc ind
  | .pi' _ _ a b => a.hasIndOcc ind || b.hasIndOcc ind
  | .proj _ a => a.hasIndOcc ind
  | .letE _ a b c => a.hasIndOcc ind || b.hasIndOcc ind || c.hasIndOcc ind
  | .mvar _ => false

def Ty.hasIndOcc {n : Nat} (ind : Name) : Ty n → Bool
  | .u _ => false
  | .pi _ _ a b => a.hasIndOcc ind || b.hasIndOcc ind
  | .el a => a.hasIndOcc ind

end

def Ctx.shiftAt {a b : Nat} (cutoff s : Nat) (tele : Ctx a b) : Ctx (a + s) (b + s) :=
  tele.dmap s fun {n : Nat} ⟨name, bi, ty⟩ => ⟨name, bi, ty.shiftAfter (n + cutoff) s⟩

def Ctx.shift {m k : Nat} := @Ctx.shiftAt m k 0

def shiftIndexTys {a k : Nat} (s : Nat) : Ctx a k → Ctx (a + s) (k + s)
  | .nil => Tele.nil
  | .snoc (b := n) bs ⟨name, bi, ty⟩ =>
      have : n + s + 1 = n + 1 + s := by omega
      this ▸ (shiftIndexTys s bs).snoc ⟨name, bi, ty.shiftAfter (n - a) s⟩

end Qdt
