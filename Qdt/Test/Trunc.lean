import Qdt.Test

open Qdt

/-! ## `trunc.rec` β-reduction on `trunc.tr` -/

#pass (
  inductive Eq.{u} (α : Type u) (a : α) : α → Type u where
    | refl : Eq α a a

  axiom trunc_index : Type
  axiom is_trunc.{u} (n : trunc_index) (α : Type u) : Type u

  axiom trunc.{u} (n : trunc_index) (α : Type u) : Type u
  axiom trunc.tr.{u} (n : trunc_index) (α : Type u) (a : α) : trunc.{u} n α
  axiom trunc.rec.{u, v}
      (n : trunc_index)
      (α : Type u)
      (P : trunc.{u} n α → Type v)
      (Pt : (aa : trunc.{u} n α) → is_trunc.{v} n (P aa))
      (H : (a : α) → P (trunc.tr.{u} n α a))
      (t : trunc.{u} n α) :
      P t

  def rec_tr.{u, v}
      (n : trunc_index)
      (α : Type u)
      (P : trunc.{u} n α → Type v)
      (Pt : (aa : trunc.{u} n α) → is_trunc.{v} n (P aa))
      (H : (a : α) → P (trunc.tr.{u} n α a))
      (a : α) :
      Eq.{v} (P (trunc.tr.{u} n α a))
        (trunc.rec.{u, v} n α P Pt H (trunc.tr.{u} n α a)) (H a) :=
    Eq.refl.{v} (P (trunc.tr.{u} n α a)) (H a)
)

/-! ## Reduction under an outer function -/

#pass (
  inductive Eq.{u} (α : Type u) (a : α) : α → Type u where
    | refl : Eq α a a

  axiom trunc_index : Type
  axiom is_trunc.{u} (n : trunc_index) (α : Type u) : Type u

  axiom trunc.{u} (n : trunc_index) (α : Type u) : Type u
  axiom trunc.tr.{u} (n : trunc_index) (α : Type u) (a : α) : trunc.{u} n α
  axiom trunc.rec.{u, v}
      (n : trunc_index)
      (α : Type u)
      (P : trunc.{u} n α → Type v)
      (Pt : (aa : trunc.{u} n α) → is_trunc.{v} n (P aa))
      (H : (a : α) → P (trunc.tr.{u} n α a))
      (t : trunc.{u} n α) :
      P t

  def rec_tr_under_fn.{u, v}
      (n : trunc_index)
      (α : Type u)
      (β : Type v)
      (Bt : is_trunc.{v} n β)
      (g : β → β)
      (f : α → β)
      (a : α) :
      Eq.{v} β
        (g (trunc.rec.{u, v} n α (fun (_ : trunc.{u} n α) => β)
              (fun (_ : trunc.{u} n α) => Bt) f (trunc.tr.{u} n α a)))
        (g (f a)) :=
    Eq.refl.{v} β (g (f a))
)

/-! ## `trunc.elim` defined via `trunc.rec` reduces on `trunc.tr` -/

#pass (
  inductive Eq.{u} (α : Type u) (a : α) : α → Type u where
    | refl : Eq α a a

  axiom trunc_index : Type
  axiom is_trunc.{u} (n : trunc_index) (α : Type u) : Type u

  axiom trunc.{u} (n : trunc_index) (α : Type u) : Type u
  axiom trunc.tr.{u} (n : trunc_index) (α : Type u) (a : α) : trunc.{u} n α
  axiom trunc.rec.{u, v}
      (n : trunc_index)
      (α : Type u)
      (P : trunc.{u} n α → Type v)
      (Pt : (aa : trunc.{u} n α) → is_trunc.{v} n (P aa))
      (H : (a : α) → P (trunc.tr.{u} n α a))
      (t : trunc.{u} n α) :
      P t

  def elim.{u, v}
      (n : trunc_index)
      (α : Type u)
      (β : Type v)
      (Bt : is_trunc.{v} n β)
      (f : α → β)
      (t : trunc.{u} n α) :
      β :=
    trunc.rec.{u, v} n α (fun (_ : trunc.{u} n α) => β)
      (fun (_ : trunc.{u} n α) => Bt) f t

  def elim_tr.{u, v}
      (n : trunc_index)
      (α : Type u)
      (β : Type v)
      (Bt : is_trunc.{v} n β)
      (f : α → β)
      (a : α) :
      Eq.{v} β (elim.{u, v} n α β Bt f (trunc.tr.{u} n α a)) (f a) :=
    Eq.refl.{v} β (f a)
)

/-! ## Reduction at concrete universe instantiations -/

#pass (
  inductive Eq.{u} (α : Type u) (a : α) : α → Type u where
    | refl : Eq α a a

  inductive Nat : Type where
    | zero
    | succ (n : Nat)

  axiom trunc_index : Type
  axiom is_trunc.{u} (n : trunc_index) (α : Type u) : Type u
  axiom is_trunc_nat (n : trunc_index) : is_trunc.{0} n Nat

  axiom trunc.{u} (n : trunc_index) (α : Type u) : Type u
  axiom trunc.tr.{u} (n : trunc_index) (α : Type u) (a : α) : trunc.{u} n α
  axiom trunc.rec.{u, v}
      (n : trunc_index)
      (α : Type u)
      (P : trunc.{u} n α → Type v)
      (Pt : (aa : trunc.{u} n α) → is_trunc.{v} n (P aa))
      (H : (a : α) → P (trunc.tr.{u} n α a))
      (t : trunc.{u} n α) :
      P t

  def succ_of_tr (n : trunc_index) (k : Nat) :
      Eq.{0} Nat
        (trunc.rec.{0, 0} n Nat (fun (_ : trunc.{0} n Nat) => Nat)
          (fun (_ : trunc.{0} n Nat) => is_trunc_nat n) Nat.succ
          (trunc.tr.{0} n Nat k))
        (Nat.succ k) :=
    Eq.refl.{0} Nat (Nat.succ k)
)
