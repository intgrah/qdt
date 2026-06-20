import Qdt.Test

#pass (
  inductive List.{u} (α : Type u) : Type u where
    | nil
    | cons (head : α) (tail : List α)

  def List.foldl.{u, v} {α : Type u} {β : Type v} (f : β → α → β) (z : β) (xs : List α) : β :=
    List.rec (fun acc => acc) (fun h _ ih acc => ih (f acc h)) xs z
)
