set_option hygiene false

notation "𝑢" => Ty.u
notation "Π'" => Ty.pi
notation "S'" => Ty.sigma
notation "El" => Ty.el
notation "True'" => Ty.true
notation "Eq'" => Ty.eq

notation "π" => Tm.piHat
notation "σ" => Tm.sigmaHat
notation "λ'" => Tm.lam
notation "mkΣ" => Tm.mkSigma
notation "true" => Tm.true
notation "eq" => Tm.eqHat
notation "refl" => Tm.refl

notation:40 Γ " ⊢ " A " type" => IsType Γ A
notation:40 Γ " ⊢ " e " : " A => HasType Γ e A
notation:40 Γ " ⊢ " A " ≡ " B => TyEq Γ A B

mutual
  inductive Ty where
    | u : Ty
    | pi : Ty → Ty → Ty  -- Π(A x. B{x}) where B is in context A :: Γ
    | sigma : Ty → Ty → Ty  -- Σ(A x. B{x}) where B is in context A :: Γ
    | el : Tm → Ty  -- El(A) : Ty where A : Tm(U)
    | true : Ty  -- True type
    | eq : Ty → Tm → Tm → Ty  -- Eq(A, a, b) where A : Ty, a : A, b : A
  deriving Repr

  inductive Tm where
    | var : Nat → Tm -- de Bruijn index
    | piHat : Tm → Tm → Tm  -- π(a x. b{x}) where b is in context El(a) :: Γ
    | sigmaHat : Tm → Tm → Tm  -- σ(a x. b{x}) where b is in context El(a) :: Γ
    | lam : Ty → Ty → Tm → Tm  -- λ(A x. B{x}, t{x}) where B and t are in context A :: Γ
    | app : Tm → Tm → Tm
    | mkSigma : Ty → Ty → Tm → Tm → Tm  -- mkΣ(A x. B{x}, t, u) where t : A and u : B{t}
    | proj₁ : Tm → Tm  -- proj₁(t) where t : Σ(A x. B{x})
    | proj₂ : Tm → Tm  -- proj₂(t) where t : Σ(A x. B{x})
    | true : Tm  -- true : U (the term representing True in the universe)
    | trivial : Tm  -- trivial : True (the constructor for True)
    | eqHat : Tm → Tm → Tm → Tm  -- eq(A, a, b) : U where A : U, a : El(A), b : El(A)
    | refl : Ty → Tm → Tm  -- refl(A, a) : Eq(A, a, a) where A : Ty, a : A
  deriving Repr
end

def Ctx := List Ty

mutual
  def subst_ty (u : Tm) : Ty → Ty
    | 𝑢 => 𝑢
    | Π' A B' => Π' (subst_ty (shift_tm u) A) (subst_ty (shift_tm u) B')
    | S' A B' => S' (subst_ty (shift_tm u) A) (subst_ty (shift_tm u) B')
    | El a => El (subst_tm (shift_tm u) a)
    | True' => True'
    | Eq' A a b => Eq' (subst_ty (shift_tm u) A) (subst_tm (shift_tm u) a) (subst_tm (shift_tm u) b)

  def subst_tm (u : Tm) : Tm → Tm
    | Tm.var 0 => u
    | Tm.var (n + 1) => Tm.var n
    | π a b => π (subst_tm (shift_tm u) a) (subst_tm (shift_tm u) b)
    | σ a b => σ (subst_tm (shift_tm u) a) (subst_tm (shift_tm u) b)
    | λ' A B t' => λ' (subst_ty (shift_tm u) A) (subst_ty (shift_tm u) B) (subst_tm (shift_tm u) t')
    | Tm.app f x => Tm.app (subst_tm (shift_tm u) f) (subst_tm (shift_tm u) x)
    | mkΣ A B t' u' => mkΣ (subst_ty (shift_tm u) A) (subst_ty (shift_tm u) B) (subst_tm (shift_tm u) t') (subst_tm (shift_tm u) u')
    | Tm.proj₁ p => Tm.proj₁ (subst_tm (shift_tm u) p)
    | Tm.proj₂ p => Tm.proj₂ (subst_tm (shift_tm u) p)
    | true => true
    | Tm.trivial => Tm.trivial
    | eq A a b => eq (subst_tm (shift_tm u) A) (subst_tm (shift_tm u) a) (subst_tm (shift_tm u) b)
    | refl A a => refl (subst_ty (shift_tm u) A) (subst_tm (shift_tm u) a)

  def shift_ty : Ty → Ty
    | 𝑢 => 𝑢
    | Π' A' B' => Π' (shift_ty A') (shift_ty B')
    | S' A' B' => S' (shift_ty A') (shift_ty B')
    | El a => El (shift_tm a)
    | True' => True'
    | Eq' A' a b => Eq' (shift_ty A') (shift_tm a) (shift_tm b)

  def shift_tm : Tm → Tm
    | Tm.var n => Tm.var (n + 1)
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
  -- Γ ⊢ t : A
  inductive HasType : Ctx → Tm → Ty → Prop where
    | piHat {Γ a b} :
        (Γ ⊢ a : 𝑢) →
        (Ty.el a :: Γ ⊢ b : 𝑢) →
        (Γ ⊢ π a b : 𝑢)
    | lam {Γ A B t} :
        (Γ ⊢ A type) →
        (A :: Γ ⊢ B type) →
        (A :: Γ ⊢ t : B) →
        (Γ ⊢ λ' A B t : Π' A B)
    | app {Γ t u A B} :
        (Γ ⊢ t : Ty.pi A B) →
        (Γ ⊢ u : A) →
        (Γ ⊢ Tm.app t u : subst_ty u B)  -- B{u}
    -- Γ ⊢ mkΣ(A, B{x}, t, u) : Σ(A, B{x}) where Γ ⊢ t : A, Γ ⊢ u : B{t}
    | mkSigma {Γ A B t u} :
        (Γ ⊢ A type) →
        (A :: Γ ⊢ B type) →
        (Γ ⊢ t : A) →
        (Γ ⊢ u : subst_ty t B) →  -- B{t}
        (Γ ⊢ mkΣ A B t u : S' A B)
    -- Γ ⊢ π₁(t) : A where Γ ⊢ t : Σ(A, B{x})
    | proj1 {Γ t A B} :
        (Γ ⊢ t : S' A B) →
        (Γ ⊢ Tm.proj₁ t : A)
    -- Γ ⊢ π₂(t) : B{π₁(t)} where Γ ⊢ t : Σ(A, B{x})
    | proj2 {Γ t A B} :
        (Γ ⊢ t : S' A B) →
        (Γ ⊢ Tm.proj₂ t : subst_ty (Tm.proj₁ t) B)  -- B{π₁(t)}
    -- Γ ⊢ σ(a, b{x}) : U where Γ ⊢ a : U, Γ, x : El(a) ⊢ b{x} : U
    | sigmaHat {Γ a b} :
        (Γ ⊢ a : 𝑢) →
        (El a :: Γ ⊢ b : 𝑢) →
        (Γ ⊢ σ a b : 𝑢)
    -- Γ ⊢ true : U
    | true {Γ} :
        (Γ ⊢ true : 𝑢)
    -- Γ ⊢ trivial : True
    | trivial {Γ} :
        (Γ ⊢ Tm.trivial : True')
    -- Γ ⊢ eq(A, a, b) : U where Γ ⊢ A : U, Γ ⊢ a : El(A), Γ ⊢ b : El(A)
    | eqHat {Γ A a b} :
        (Γ ⊢ A : 𝑢) →
        (Γ ⊢ a : El A) →
        (Γ ⊢ b : El A) →
        (Γ ⊢ eq A a b : 𝑢)
    -- Γ ⊢ refl(A, a) : Eq(A, a, a) where Γ ⊢ A type, Γ ⊢ a : A
    | refl {Γ A a} :
        (Γ ⊢ A type) →
        (Γ ⊢ a : A) →
        (Γ ⊢ refl A a : Eq' A a a)

  -- Γ ⊢ A type
  inductive IsType : Ctx → Ty → Prop where
    | u {Γ} :
        (Γ ⊢ 𝑢 type) -- Γ ⊢ U type
    | el {Γ A} :
        (Γ ⊢ A : 𝑢) →
        (Γ ⊢ Ty.el A type) -- Γ ⊢ El(A) type
    | pi {Γ A B} :
        (Γ ⊢ A type) →
        (A :: Γ ⊢ B type) →
        (Γ ⊢ Π' A B type) -- Γ ⊢ Π(A, B{x}) type
    -- Γ ⊢ Σ(A, B{x}) type where Γ ⊢ A type, Γ, x : A ⊢ B{x} type
    | sigma {Γ A B} :
        (Γ ⊢ A type) →
        (A :: Γ ⊢ B type) →
        (Γ ⊢ S' A B type)
    -- Γ ⊢ True type
    | true {Γ} :
        (Γ ⊢ True' type)
    -- Γ ⊢ Eq(A, a, b) type where Γ ⊢ A type, Γ ⊢ a : A, Γ ⊢ b : A
    | eq {Γ A a b} :
        (Γ ⊢ A type) →
        (Γ ⊢ a : A) →
        (Γ ⊢ b : A) →
        (Γ ⊢ Eq' A a b type)
end

-- Γ ⊢ A ≡ B
inductive TyEq : Ctx → Ty → Ty → Prop where
  | refl {Γ A} :
      (Γ ⊢ A ≡ A)
  | symm {Γ A B} :
      (Γ ⊢ A ≡ B) →
      (Γ ⊢ B ≡ A)
  | trans {Γ A B C} :
      (Γ ⊢ A ≡ B) →
      (Γ ⊢ B ≡ C) →
      (Γ ⊢ A ≡ C)
  | el_pi {Γ a b} :
      (Γ ⊢ El (π a b) ≡ Π' (El a) (El b))
  | el_sigma {Γ a b} :
      (Γ ⊢ El (σ a b) ≡ S' (El a) (El b))
