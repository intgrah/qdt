import Qdt.Test

#pass (
  inductive List.{u} (α : Type u) : Type u where
    | nil
    | cons (head : α) (tail : List α)

  inductive List.Perm.{u} {α : Type u} : List α → List α → Type u where
    | nil : List.Perm List.nil List.nil
    | cons (x : α) {l₁ l₂ : List α} : List.Perm l₁ l₂ → List.Perm (List.cons x l₁) (List.cons x l₂)
    | swap
        (x y : α) (l : List α) :
        List.Perm (List.cons y (List.cons x l)) (List.cons x (List.cons y l))
    | trans {l₁ l₂ l₃ : List α} : List.Perm l₁ l₂ → List.Perm l₂ l₃ → List.Perm l₁ l₃
)
