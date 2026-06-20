import Qdt.Test

#pass (
  inductive Eq.{u} {α : Type u} : α → α → Type u where
    | refl (a : α) : Eq a a

  def Eq.subst.{v, u} {α : Type u} (P : α → Type v) {a b : α} (p : Eq a b) (h : P a) : P b :=
    @Eq.rec α a (fun x _ => P x) h b p

  def rfl.{u} {α : Type u} {a : α} : Eq a a := Eq.refl a

  def congrArg.{u, v} {α : Type u} {β : Type v} (g : α → β) {a₁ a₂ : α} (h : Eq a₁ a₂) :
      Eq (g a₁) (g a₂) :=
    Eq.subst (fun z => Eq (g a₁) (g z)) h rfl

  structure Box.{u, v} (f : Type u → Type v) : Type (max (u + 1) v) where
    (ap {α β : Type u} : f (α → β) → f α → f β)
    (tri {α β : Type u} : f (α → β) → f α → f α → f β)

  def apCongr.{u, v} {f : Type u → Type v} (inst : Box f) {α γ : Type u}
      (x : f α) (p q : f (α → γ)) (h : Eq p q) :
      Eq (Box.ap inst p x) (Box.ap inst q x) :=
    congrArg (fun k : f (α → γ) => Box.ap inst k x) h

  def apCongrLam.{u, v} {f : Type u → Type v} (inst : Box f) {α γ : Type u}
      (p q : f (α → γ)) (h : Eq p q) :
      Eq (fun (w : f α) => Box.ap inst p w) (fun (w : f α) => Box.ap inst q w) :=
    congrArg (fun k : f (α → γ) => fun (w : f α) => Box.ap inst k w) h

  def triCongrLam.{u, v} {f : Type u → Type v} (inst : Box f) {α γ : Type u}
      (p q : f (α → γ)) (h : Eq p q) :
      Eq (fun (w1 w2 : f α) => Box.tri inst p w1 w2)
         (fun (w1 w2 : f α) => Box.tri inst q w1 w2) :=
    congrArg (fun k : f (α → γ) => fun (w1 w2 : f α) => Box.tri inst k w1 w2) h
)
