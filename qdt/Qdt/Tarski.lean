set_option hygiene false

notation "𝑢" => Ty.U
notation "Π'" => Ty.Pi
notation "S'" => Ty.Sigma
notation "El" => Ty.El
notation "Unit" => Ty.Unit
notation "Eq'" => Ty.Eq

prefix:max "#" => Tm.var
notation "π" => Tm.Ty.pi
notation "σ" => Tm.Ty.sigma
notation "λ'" => Tm.lambda
notation "mkΣ" => Tm.mkSigma
notation "unit" => Tm.Ty.unit
notation "()" => Tm.unit
notation "eq" => Tm.Ty.eq
notation "refl" => Tm.refl
infixl:67 "; " => Ctx.snoc
notation:max A "[" u "]" => Ty.subst u A
notation:max t "[" u "]" => Tm.subst u t

notation:40 Γ " ⊢ " A " type" => Ty.Wf Γ A
notation:40 Γ " ⊢ " e " : " A => Tm.Wf Γ e A
notation:40 Γ " ⊢ " A " ≡ " B => Ty.Equal Γ A B
notation:40 Γ " ⊢ " e " ⇐ " A => Check Γ e A
notation:40 Γ " ⊢ " e " ⇒ " A => Infer Γ e A

mutual

inductive Ty : Nat → Type where
  | U : Ty n
  | Pi : Ty n → Ty (n + 1) → Ty n  -- Π(A x. B{x}) where B is in context Γ, A
  | Sigma : Ty n → Ty (n + 1) → Ty n  -- Σ(A x. B{x}) where B is in context Γ, A
  | El : Tm n → Ty n  -- El(A) : Ty where A : Tm(U)
  | Unit : Ty n  -- True type
  | Eq : Ty n → Tm n → Tm n → Ty n  -- Eq(A, a, b) where A : Ty, a : A, b : A

inductive Tm : Nat → Type where
  | var : Fin n → Tm n -- de Bruijn index
  | Ty.pi : Tm n → Tm (n + 1) → Tm n  -- π(a x. b{x}) where b is in context Γ, El(a)
  | Ty.sigma : Tm n → Tm (n + 1) → Tm n  -- σ(a x. b{x}) where b is in context Γ, El(a)
  | lambda : Tm (n + 1) → Tm n  -- λ(A x. B{x}, t{x}) where B and t are in context Γ, A
  | app : Tm n → Tm n → Tm n
  | mkSigma : Ty n → Ty (n + 1) → Tm n → Tm n → Tm n  -- mkΣ(A x. B{x}, t, u) where t : A and u : B{t}
  | proj₁ : Tm n → Tm n  -- proj₁(t) where t : Σ(A x. B{x})
  | proj₂ : Tm n → Tm n  -- proj₂(t) where t : Σ(A x. B{x})
  | Ty.unit : Tm n  -- unit' : U (El(unit') = Unit)
  | unit : Tm n  -- unit : Unit (the constructor for True)
  | Ty.eq : Tm n → Tm n → Tm n → Tm n  -- eq(A, a, b) : U where A : U, a : El(A), b : El(A)
  | refl : Ty n → Tm n → Tm n  -- refl(A, a) : Eq(A, a, a) where A : Ty, a : A
  | anno : Tm n → Ty n → Tm n  -- (e : A)

end

mutual

def Ty.weaken : Ty n → Ty (n + 1)
  | 𝑢 => 𝑢
  | Π' A' B' => Π' A'.weaken B'.weaken
  | S' A' B' => S' A'.weaken B'.weaken
  | El a => El a.weaken
  | Unit => Unit
  | Eq' A' a b => Eq' A'.weaken a.weaken b.weaken

def Tm.weaken : Tm n → Tm (n + 1)
  | #⟨i, h⟩ => Tm.var ⟨i + 1, Nat.succ_lt_succ h⟩
  | π a b => π a.weaken b.weaken
  | σ a b => σ a.weaken b.weaken
  | λ' t => λ' t.weaken
  | Tm.app f x => Tm.app f.weaken x.weaken
  | mkΣ A B t u => mkΣ A.weaken B.weaken t.weaken u.weaken
  | Tm.proj₁ p => Tm.proj₁ p.weaken
  | Tm.proj₂ p => Tm.proj₂ p.weaken
  | unit => unit
  | () => ()
  | eq A a b => eq A.weaken a.weaken b.weaken
  | refl A a => refl A.weaken a.weaken
  | Tm.anno e A => Tm.anno e.weaken A.weaken

end

/--
Type contexts.

⊢ Γ ctx
-/
inductive Ctx : Nat → Type where
  | nil : Ctx 0
  | snoc : Ctx n → Ty n → Ctx (n + 1)

def Ctx.get : Ctx n → Fin n → Ty n
  | _; ty, 0 => ty.weaken
  | ctx; _, ⟨i + 1, h⟩ => ctx.get ⟨i, Nat.lt_of_succ_lt_succ h⟩ |>.weaken

mutual

def Ty.subst (u : Tm n) : Ty (n + 1) → Ty n
  | 𝑢 => 𝑢
  | Π' A B' => Π' A[u] B'[u.weaken]
  | S' A B' => S' A[u] B'[u.weaken]
  | El a => El a[u]
  | Unit => Unit
  | Eq' A a b => Eq' A[u] a[u] b[u]

def Tm.subst (u : Tm n) : Tm (n + 1) → Tm n
  | Tm.var ⟨0, _⟩ => u
  | Tm.var ⟨i + 1, h⟩ => Tm.var ⟨i, Nat.lt_of_succ_lt_succ h⟩
  | π a b => π a[u] b[u.weaken]
  | σ a b => σ a[u] b[u.weaken]
  | λ' t' => λ' t'[u.weaken]
  | Tm.app f x => Tm.app f[u] x[u]
  | mkΣ A B t' u' => mkΣ A[u] B[u.weaken] t'[u] u'[u]
  | Tm.proj₁ p => Tm.proj₁ p[u]
  | Tm.proj₂ p => Tm.proj₂ p[u]
  | unit => unit
  | () => ()
  | eq A a b => eq A[u] a[u] b[u]
  | refl A a => refl A[u] a[u]
  | Tm.anno e A => Tm.anno e[u] A[u]

end

mutual

/--
Type well-foundedness.

Γ ⊢ A type

In a context Γ, A is a well formed type.
-/
inductive Ty.Wf : Ctx n → Ty n → Prop where
  | U {Γ : Ctx n} :
      (Γ ⊢ 𝑢 type)
  | El {Γ : Ctx n} {A} :
      (Γ ⊢ A : 𝑢) →
      (Γ ⊢ El A type)
  | Pi {Γ : Ctx n} {A B} :
      (Γ ⊢ A type) →
      (Γ; A ⊢ B type) →
      (Γ ⊢ Π' A B type)
  | Sigma {Γ : Ctx n} {A B} :
      (Γ ⊢ A type) →
      (Γ; A ⊢ B type) →
      (Γ ⊢ S' A B type)
  | Unit {Γ : Ctx n} :
      (Γ ⊢ Unit type)
  | Eq {Γ : Ctx n} {A a b} :
      (Γ ⊢ A type) →
      (Γ ⊢ a : A) →
      (Γ ⊢ b : A) →
      (Γ ⊢ Eq' A a b type)

/--
Term well-foundedness.

Γ ⊢ t : A

In a context Γ, t has type A.
-/
inductive Tm.Wf : Ctx n → Tm n → Ty n → Prop where
  | var {Γ : Ctx n} {i} :
      (Γ ⊢ .var i : Γ.get i)
  | pi {Γ : Ctx n} {a b} :
      (Γ ⊢ a : 𝑢) →
      (Γ; El a ⊢ b : 𝑢) →
      (Γ ⊢ π a b : 𝑢)
  | lambda {Γ : Ctx n} {A B t} :
      (Γ ⊢ A type) →
      (Γ; A ⊢ B type) →
      (Γ; A ⊢ t : B) →
      (Γ ⊢ λ' t : Π' A B)
  | app {Γ : Ctx n} {f a A B} :
      (Γ ⊢ f : Π' A B) →
      (Γ ⊢ a : A) →
      (Γ ⊢ f.app a : B[a])
  | mkSigma {Γ : Ctx n} {A B t u} :
      (Γ ⊢ A type) →
      (Γ; A ⊢ B type) →
      (Γ ⊢ t : A) →
      (Γ ⊢ u : B[t]) →
      (Γ ⊢ mkΣ A B t u : S' A B)
  | proj₁ {Γ : Ctx n} {t A B} :
      (Γ ⊢ t : S' A B) →
      (Γ ⊢ t.proj₁ : A)
  | proj₂ {Γ : Ctx n} {t A B} :
      (Γ ⊢ t : S' A B) →
      (Γ ⊢ t.proj₂ : B[t.proj₁])
  | sigma {Γ : Ctx n} {a b} :
      (Γ ⊢ a : 𝑢) →
      (Γ; El a ⊢ b : 𝑢) →
      (Γ ⊢ σ a b : 𝑢)
  | unit' {Γ : Ctx n} :
      (Γ ⊢ unit : 𝑢)
  | unit {Γ : Ctx n} :
      (Γ ⊢ () : Unit)
  | eq {Γ : Ctx n} {A a b} :
      (Γ ⊢ A : 𝑢) →
      (Γ ⊢ a : El A) →
      (Γ ⊢ b : El A) →
      (Γ ⊢ eq A a b : 𝑢)
  | refl {Γ : Ctx n} {A a} :
      (Γ ⊢ A type) →
      (Γ ⊢ a : A) →
      (Γ ⊢ refl A a : Eq' A a a)
  | conv {Γ : Ctx n} {t A B} :
      (Γ ⊢ t : A) →
      (Γ ⊢ A ≡ B) →
      (Γ ⊢ t : B)

/--
Judgemental equality of types.

Γ ⊢ A ≡ B

In a context Γ, A and B are deemed to be equal types.
-/
inductive Ty.Equal : Ctx n → Ty n → Ty n → Prop where
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

end

mutual

/--
Bidirectional type checking: checking mode.

Γ ⊢ t ⇐ A

In a context Γ, t checks with type A.
-/
inductive Check : Ctx n → Tm n → Ty n → Prop where
  | unit {Γ : Ctx n} :
      (Γ ⊢ () ⇐ Unit)
  | lam {Γ : Ctx n} {e A B} :
      (Γ; A ⊢ e ⇐ B) →
      (Γ ⊢ λ' e ⇐ Π' A B)

/--
Bidirectional type checking: inference mode.

Γ ⊢ t ⇒ A

In a context Γ, t infers type A.
-/
inductive Infer : Ctx n → Tm n → Ty n → Prop where
  | var {Γ : Ctx n} {i} :
      Infer Γ (.var i) (Γ.get i)
  | unit {Γ : Ctx n} :
      (Γ ⊢ () ⇒ Unit)

end
