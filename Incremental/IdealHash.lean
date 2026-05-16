module

public import Incremental.Basic
public import Mathlib.Logic.Embedding.Basic

@[expose] public section

class IdealHashable (α : Type) [Hashable α] : Prop where
  inj : Function.Injective (hash : α → UInt64)

axiom Hashable.ideal {α : Type} [Hashable α] : IdealHashable α

attribute [instance] Hashable.ideal

@[inline] def Hashable.toEmbedding {α : Type} [Hashable α] [IdealHashable α] :
    α ↪ UInt64 :=
  ⟨hash, IdealHashable.inj⟩

theorem Hashable.ideal_false : False := by
  have hcollide : hash 0 = hash (2 ^ 64) := rfl
  have : 0 = 2 ^ 64 := IdealHashable.inj hcollide
  -- Famously, 0 is not 2 ^ 64
  omega
