set_option hygiene false

notation "𝑢" => Ty.U
notation "Π'" => Ty.Pi
notation "S'" => Ty.Sigma
notation "El" => Ty.El
notation "True'" => Ty.True
notation "Eq'" => Ty.Eq

notation "π" => Tm.pi
notation "σ" => Tm.sigma
notation "λ'" => Tm.lambda
notation "mkΣ" => Tm.mkSigma
notation "true" => Tm.true
notation "eq" => Tm.eq
notation "refl" => Tm.refl

infixl:67 "; " => Ctx.snoc
notation:max A "[" u "]" => subst_ty u A
notation:max t "[" u "]" => subst_tm u t

notation:40 Γ " ⊢ " A " type" => IsType Γ A
notation:40 Γ " ⊢ " e " : " A => HasType Γ e A
notation:40 Γ " ⊢ " A " ≡ " B => TyEq Γ A B

mutual
  inductive Ty : Nat → Type where
    | U : Ty n
    | Pi : Ty n → Ty (n + 1) → Ty n  -- Π(A x. B{x}) where B is in context Γ, A
    | Sigma : Ty n → Ty (n + 1) → Ty n  -- Σ(A x. B{x}) where B is in context Γ, A
    | El : Tm n → Ty n  -- El(A) : Ty where A : Tm(U)
    | True : Ty n  -- True type
    | Eq : Ty n → Tm n → Tm n → Ty n  -- Eq(A, a, b) where A : Ty, a : A, b : A
  deriving Repr

  inductive Tm : Nat → Type where
    | var : Fin n → Tm n -- de Bruijn index
    | pi : Tm n → Tm (n + 1) → Tm n  -- π(a x. b{x}) where b is in context Γ, El(a)
    | sigma : Tm n → Tm (n + 1) → Tm n  -- σ(a x. b{x}) where b is in context Γ, El(a)
    | lambda : Ty n → Ty (n + 1) → Tm (n + 1) → Tm n  -- λ(A x. B{x}, t{x}) where B and t are in context Γ, A
    | app : Tm n → Tm n → Tm n
    | mkSigma : Ty n → Ty (n + 1) → Tm n → Tm n → Tm n  -- mkΣ(A x. B{x}, t, u) where t : A and u : B{t}
    | proj₁ : Tm n → Tm n  -- proj₁(t) where t : Σ(A x. B{x})
    | proj₂ : Tm n → Tm n  -- proj₂(t) where t : Σ(A x. B{x})
    | true : Tm n  -- true : U (the term representing True in the universe)
    | trivial : Tm n  -- trivial : True (the constructor for True)
    | eq : Tm n → Tm n → Tm n → Tm n  -- eq(A, a, b) : U where A : U, a : El(A), b : El(A)
    | refl : Ty n → Tm n → Tm n  -- refl(A, a) : Eq(A, a, a) where A : Ty, a : A
  deriving Repr
end

inductive Ctx : Nat → Type where
  | nil : Ctx 0
  | snoc : Ctx n → Ty n → Ctx (n + 1)

mutual
  def shift_ty : Ty n → Ty (n + 1)
    | 𝑢 => 𝑢
    | Π' A' B' => Π' (shift_ty A') (shift_ty B')
    | S' A' B' => S' (shift_ty A') (shift_ty B')
    | El a => El (shift_tm a)
    | True' => True'
    | Eq' A' a b => Eq' (shift_ty A') (shift_tm a) (shift_tm b)

  def shift_tm : Tm n → Tm (n + 1)
    | Tm.var ⟨i, h⟩ => Tm.var ⟨i + 1, Nat.succ_lt_succ h⟩
    | π a b => π (shift_tm a) (shift_tm b)
    | σ a b => σ (shift_tm a) (shift_tm b)
    | λ' A B t' => λ' (shift_ty A) (shift_ty B) (shift_tm t')
    | Tm.app f x => Tm.app (shift_tm f) (shift_tm x)
    | mkΣ A B t' u' => mkΣ (shift_ty A) (shift_ty B) (shift_tm t') (shift_tm u')
    | Tm.proj₁ p => Tm.proj₁ (shift_tm p)
    | Tm.proj₂ p => Tm.proj₂ (shift_tm p)
    | true => true
    | Tm.trivial => Tm.trivial
    | eq A a b => eq (shift_tm A) (shift_tm a) (shift_tm b)
    | refl A a => refl (shift_ty A) (shift_tm a)
end

mutual
  def subst_ty (u : Tm n) : Ty (n + 1) → Ty n
    | 𝑢 => 𝑢
    | Π' A B' => Π' A[u] B'[shift_tm u]
    | S' A B' => S' A[u] B'[shift_tm u]
    | El a => El a[u]
    | True' => True'
    | Eq' A a b => Eq' A[u] a[u] b[u]

  def subst_tm (u : Tm n) : Tm (n + 1) → Tm n
    | Tm.var ⟨0, _⟩ => u
    | Tm.var ⟨i + 1, h⟩ => Tm.var ⟨i, Nat.lt_of_succ_lt_succ h⟩
    | π a b => π a[u] b[shift_tm u]
    | σ a b => σ a[u] b[shift_tm u]
    | λ' A B t' => λ' A[u] B[shift_tm u] t'[shift_tm u]
    | Tm.app f x => Tm.app f[u] x[u]
    | mkΣ A B t' u' => mkΣ A[u] B[shift_tm u] t'[u] u'[u]
    | Tm.proj₁ p => Tm.proj₁ p[u]
    | Tm.proj₂ p => Tm.proj₂ p[u]
    | true => true
    | Tm.trivial => Tm.trivial
    | eq A a b => eq A[u] a[u] b[u]
    | refl A a => refl A[u] a[u]
end

mutual
  -- Γ ⊢ t : A
  inductive HasType : Ctx n → Tm n → Ty n → Prop where
    | pi {Γ : Ctx n} {a b} :
        (Γ ⊢ a : 𝑢) →
        (Γ; El a ⊢ b : 𝑢) →
        (Γ ⊢ π a b : 𝑢)
    | lambda {Γ : Ctx n} {A B t} :
        (Γ ⊢ A type) →
        (Γ; A ⊢ B type) →
        (Γ; A ⊢ t : B) →
        (Γ ⊢ λ' A B t : Π' A B)
    | app {Γ : Ctx n} {t u A B} :
        (Γ ⊢ t : Π' A B) →
        (Γ ⊢ u : A) →
        (Γ ⊢ Tm.app t u : B[u])
    -- Γ ⊢ mkΣ(A, B{x}, t, u) : Σ(A, B{x}) where Γ ⊢ t : A, Γ ⊢ u : B[t]
    | mkSigma {Γ : Ctx n} {A B t u} :
        (Γ ⊢ A type) →
        (Γ; A ⊢ B type) →
        (Γ ⊢ t : A) →
        (Γ ⊢ u : B[t]) →
        (Γ ⊢ mkΣ A B t u : S' A B)
    -- Γ ⊢ π₁(t) : A where Γ ⊢ t : Σ(A, B{x})
    | proj₁ {Γ : Ctx n} {t A B} :
        (Γ ⊢ t : S' A B) →
        (Γ ⊢ Tm.proj₁ t : A)
    -- Γ ⊢ π₂(t) : B[π₁(t)] where Γ ⊢ t : Σ(A, B{x})
    | proj₂ {Γ : Ctx n} {t A B} :
        (Γ ⊢ t : S' A B) →
        (Γ ⊢ Tm.proj₂ t : B[Tm.proj₁ t])
    -- Γ ⊢ σ(a, b{x}) : U where Γ ⊢ a : U, Γ; El(a) ⊢ b{x} : U
    | sigma {Γ : Ctx n} {a b} :
        (Γ ⊢ a : 𝑢) →
        (Γ; El a ⊢ b : 𝑢) →
        (Γ ⊢ σ a b : 𝑢)
    -- Γ ⊢ true : U
    | true {Γ : Ctx n} :
        (Γ ⊢ true : 𝑢)
    -- Γ ⊢ trivial : True
    | trivial {Γ : Ctx n} :
        (Γ ⊢ Tm.trivial : True')
    -- Γ ⊢ eq(A, a, b) : U where Γ ⊢ A : U, Γ ⊢ a : El(A), Γ ⊢ b : El(A)
    | eq {Γ : Ctx n} {A a b} :
        (Γ ⊢ A : 𝑢) →
        (Γ ⊢ a : El A) →
        (Γ ⊢ b : El A) →
        (Γ ⊢ eq A a b : 𝑢)
    -- Γ ⊢ refl(A, a) : Eq(A, a, a) where Γ ⊢ A type, Γ ⊢ a : A
    | refl {Γ : Ctx n} {A a} :
        (Γ ⊢ A type) →
        (Γ ⊢ a : A) →
        (Γ ⊢ refl A a : Eq' A a a)

  -- Γ ⊢ A type
  inductive IsType : Ctx n → Ty n → Prop where
    | u {Γ : Ctx n} :
        (Γ ⊢ 𝑢 type) -- Γ ⊢ U type
    | el {Γ : Ctx n} {A} :
        (Γ ⊢ A : 𝑢) →
        (Γ ⊢ El A type) -- Γ ⊢ El(A) type
    | pi {Γ : Ctx n} {A B} :
        (Γ ⊢ A type) →
        (Γ; A ⊢ B type) →
        (Γ ⊢ Π' A B type) -- Γ ⊢ Π(A, B{x}) type
    -- Γ ⊢ Σ(A, B{x}) type where Γ ⊢ A type, Γ; A ⊢ B{x} type
    | sigma {Γ : Ctx n} {A B} :
        (Γ ⊢ A type) →
        (Γ; A ⊢ B type) →
        (Γ ⊢ S' A B type)
    -- Γ ⊢ True type
    | true {Γ : Ctx n} :
        (Γ ⊢ True' type)
    -- Γ ⊢ Eq(A, a, b) type where Γ ⊢ A type, Γ ⊢ a : A, Γ ⊢ b : A
    | eq {Γ : Ctx n} {A a b} :
        (Γ ⊢ A type) →
        (Γ ⊢ a : A) →
        (Γ ⊢ b : A) →
        (Γ ⊢ Eq' A a b type)
end

-- Γ ⊢ A ≡ B
inductive TyEq : Ctx n → Ty n → Ty n → Prop where
  | refl {Γ : Ctx n} {A} :
      (Γ ⊢ A ≡ A)
  | symm {Γ : Ctx n} {A B} :
      (Γ ⊢ A ≡ B) →
      (Γ ⊢ B ≡ A)
  | trans {Γ : Ctx n} {A B C} :
      (Γ ⊢ A ≡ B) →
      (Γ ⊢ B ≡ C) →
      (Γ ⊢ A ≡ C)
  | el_pi {Γ : Ctx n} {a b} :
      (Γ ⊢ El (π a b) ≡ Π' (El a) (El b))
  | el_sigma {Γ : Ctx n} {a b} :
      (Γ ⊢ El (σ a b) ≡ S' (El a) (El b))
