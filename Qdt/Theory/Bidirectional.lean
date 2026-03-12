module

public section

namespace Qdt

set_option hygiene false

notation:50 Γ " ⊩ " e " ⇐ " A => HasType.Alg.Check Γ e A
notation:50 Γ " ⊩ " e " ⇒ " A => HasType.Alg.Infer Γ e A
notation:50 Γ " ⊩ " e " ∈ " A " ⇒ " C => App.Alg Γ e A C
notation:50 Γ " ⊩ " A " ≡ " B " type" => Ty.Eq.Alg Γ A B
notation:50 Γ " ⊩ " A " type" => Ty.WF.Alg Γ A

-- mutual

-- inductive HasType.Alg.Check : {n : Nat} → Ctx 0 n → Tm n → Ty n → Prop
--   | var {Γ i A} :
--       (Γ ⊩ .var i ⇐ A)
--   | sub {n} {Γ : Ctx 0 n} {e : Tm n} {A B : Ty n} :
--       (Γ ⊩ e ⇒ A) →
--       (Γ ⊩ A ≡ B type) →
--       (Γ ⊩ e ⇐ B)
--   | lam {Γ x A body B} :
--       (Γ ⊩ A type) →
--       (Γ.snoc ⟨x, A⟩ ⊩ body ⇐ B) →
--       (Γ ⊩ .lam x A body ⇐ .pi x A B)
--   | app {Γ f a x A B C} :
--       (Γ ⊩ f ⇒ .pi x A B) →
--       (Γ ⊩ a ⇐ A) →
--       (Γ ⊩ .app f a ⇐ C)

-- inductive HasType.Alg.Infer : {n : Nat} → Ctx 0 n → Tm n → Ty n → Prop
--   | var {Γ i A} :
--       (Γ ⊩ .var i ⇒ A)
--   | const {Γ name} :
--       (Γ ⊩ .const name ⇒ 𝑢) -- TODO
--   | app {Γ f a x A B C} :
--       (Γ ⊩ f ⇒ .pi x A B) →
--       (Γ ⊩ a ⇐ A) →
--       (Γ ⊩ .app f a ⇒ C)
--   | lam {Γ x A body B} :
--       (Γ ⊩ .pi x A B type) →
--       (Γ.snoc ⟨x, A⟩ ⊩ body ⇐ B) →
--       (Γ ⊩ .lam x A body ⇒ .pi x A B)

-- inductive Ty.WF.Alg : {n : Nat} → Ctx 0 n → Ty n → Prop
--   | u {Γ} :
--       Γ ⊩ .u type
--   | el {Γ t} :
--       Γ ⊩ .el t type
--   | pi {Γ x A B} :
--       (Γ ⊩ A type) →
--       (Γ.snoc ⟨x, A⟩ ⊩ B type) →
--       (Γ ⊩ .pi x A B type)

-- inductive Ty.Eq.Alg : {n m : Nat} → Ctx 0 n → Ty n → Ty n → Ctx 0 m → Prop
--   | refl {Γ A} :
--       Γ ⊩ A ≡ A type
--   | pi {Γ x A₁ A₂ B₁ B₂} :
--       (Γ ⊩ A₁ ≡ A₂ type) →
--       (Γ ⊩ .pi x A₁ B₁ ≡ .pi x A₂ B₂ type)

-- inductive App.Alg : {n : Nat} → Ctx 0 n → Tm n → Ty n → Ty n → Prop
--   | pi {Γ e x A B C} :
--       (Γ ⊩ e ⇐ A) →
--       (Γ ⊩ e ∈ .pi x A B ⇒ C)

-- end

end Qdt
