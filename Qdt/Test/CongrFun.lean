import Qdt.Test

#pass (
  inductive Eq.{u} {α : Type u} : α → α → Type u where
    | refl (a : α) : Eq a a

  def Eq.subst.{v, u} {α : Type u} (P : α → Type v) {a b : α} (p : a = b) (h : P a) : P b :=
    @Eq.rec α a (fun x _ => P x) h b p

  def congrFun.{u, v}
      {α : Type u} {β : α → Type v} {f g : (x : α) → β x} (h : f = g) (a : α) :
      f a = g a :=
    Eq.subst (fun h => f a = h a) h (Eq.refl _)
)
