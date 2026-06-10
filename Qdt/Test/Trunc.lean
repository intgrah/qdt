import Qdt.Test

open Qdt

#pass (
  inductive Eq.{u} {α : Type u} : α → α → Type u where
    | refl (a : α) : Eq a a

  axiom trunc_index : Type
  axiom is_trunc.{u} (n : trunc_index) (α : Type u) : Type u

  axiom trunc.{u} (n : trunc_index) (α : Type u) : Type u
  axiom trunc.tr.{u} (n : trunc_index) (α : Type u) (a : α) : trunc n α
  axiom trunc.rec.{u, v}
      (n : trunc_index)
      (α : Type u)
      (P : trunc n α → Type v)
      (Pt : (aa : trunc n α) → is_trunc n (P aa))
      (H : (a : α) → P (trunc.tr n α a))
      (t : trunc n α) :
      P t

  def rec_tr.{u, v}
      (n : trunc_index)
      (α : Type u)
      (P : trunc n α → Type v)
      (Pt : (aa : trunc n α) → is_trunc n (P aa))
      (H : (a : α) → P (trunc.tr n α a))
      (a : α) :
      @trunc.rec n α P Pt H (trunc.tr n α a) = H a :=
    Eq.refl _
)

#pass (
  inductive Eq.{u} {α : Type u} : α → α → Type u where
    | refl (a : α) : Eq a a

  axiom trunc_index : Type
  axiom is_trunc.{u} (n : trunc_index) (α : Type u) : Type u

  axiom trunc.{u} (n : trunc_index) (α : Type u) : Type u
  axiom trunc.tr.{u} (n : trunc_index) (α : Type u) (a : α) : trunc n α
  axiom trunc.rec.{u, v}
      (n : trunc_index)
      (α : Type u)
      (P : trunc n α → Type v)
      (Pt : (aa : trunc n α) → is_trunc n (P aa))
      (H : (a : α) → P (trunc.tr n α a))
      (t : trunc n α) :
      P t

  def rec_tr_under_fn.{u, v}
      (n : trunc_index)
      (α : Type u)
      (β : Type v)
      (Bt : is_trunc n β)
      (g : β → β)
      (f : α → β)
      (a : α) :
      g (@trunc.rec n α (fun _ => β) (fun _ => Bt) f (trunc.tr n α a)) = g (f a) :=
    Eq.refl _
)

#pass (
  inductive Eq.{u} {α : Type u} : α → α → Type u where
    | refl (a : α) : Eq a a

  axiom trunc_index : Type
  axiom is_trunc.{u} (n : trunc_index) (α : Type u) : Type u

  axiom trunc.{u} (n : trunc_index) (α : Type u) : Type u
  axiom trunc.tr.{u} (n : trunc_index) (α : Type u) (a : α) : trunc n α
  axiom trunc.rec.{u, v}
      (n : trunc_index)
      (α : Type u)
      (P : trunc n α → Type v)
      (Pt : (aa : trunc n α) → is_trunc n (P aa))
      (H : (a : α) → P (trunc.tr n α a))
      (t : trunc n α) :
      P t

  def elim.{u, v}
      (n : trunc_index)
      (α : Type u)
      (β : Type v)
      (Bt : is_trunc n β)
      (f : α → β)
      (t : trunc n α) :
      β :=
    @trunc.rec n α (fun _ => β) (fun _ => Bt) f t

  def elim_tr.{u, v}
      (n : trunc_index)
      (α : Type u)
      (β : Type v)
      (Bt : is_trunc n β)
      (f : α → β)
      (a : α) :
      elim n α β Bt f (trunc.tr n α a) = f a :=
    Eq.refl _
)

#pass (
  inductive Eq.{u} {α : Type u} : α → α → Type u where
    | refl (a : α) : Eq a a

  inductive Nat : Type where
    | zero
    | succ (n : Nat)

  axiom trunc_index : Type
  axiom is_trunc.{u} (n : trunc_index) (α : Type u) : Type u
  axiom is_trunc_nat (n : trunc_index) : is_trunc n Nat

  axiom trunc.{u} (n : trunc_index) (α : Type u) : Type u
  axiom trunc.tr.{u} (n : trunc_index) (α : Type u) (a : α) : trunc n α
  axiom trunc.rec.{u, v}
      (n : trunc_index)
      (α : Type u)
      (P : trunc n α → Type v)
      (Pt : (aa : trunc n α) → is_trunc n (P aa))
      (H : (a : α) → P (trunc.tr n α a))
      (t : trunc n α) :
      P t

  def succ_of_tr (n : trunc_index) (k : Nat) :
    (@trunc.rec n Nat (fun _ => Nat) (fun _ => is_trunc_nat n) Nat.succ (trunc.tr n Nat k)) = Nat.succ k :=
    Eq.refl _
)
