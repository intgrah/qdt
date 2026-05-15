/-!
We can't use `module` mode here because we inspect the internals of
`ST` and `EST`, and they are not marked as `@[expose]` (for good reason).
-/

variable {ε σ : Type}

namespace ST

instance : LawfulFunctor (ST σ) := by
  constructor <;> (intros; rfl)
instance : LawfulApplicative (ST σ) := by
  constructor <;> (intros; rfl)
instance : LawfulMonad (ST σ) := by
  constructor <;> (intros; rfl)

instance : LawfulMonadAttach (ST σ) where
  map_attach := rfl
  canReturn_map_imp := by
    intro α P x a ⟨s, _, hxs⟩
    let (eq := h) ⟨⟨a, hs⟩, _⟩ := x s
    simp only [Functor.map, ST.bind, h] at hxs
    cases hxs
    exact hs

end ST

namespace EST

instance : LawfulMonad (EST ε σ) where
  map_const := rfl
  id_map x := by
    funext s
    dsimp only [Functor.map, EST.bind]
    cases x s <;> rfl
  seqLeft_eq x _ := by
    funext s
    dsimp only [SeqLeft.seqLeft, Functor.map, EST.bind, Seq.seq]
    cases x s <;> rfl
  seqRight_eq x y := by
    funext s
    dsimp only [SeqRight.seqRight, EST.bind, Seq.seq, Functor.map, Function.comp_const,
      Function.const_apply, EST.pure]
    cases hx : x s with
    | ok _ s' => dsimp only; cases y s' <;> rfl
    | error _ _ => rfl
  pure_seq _ _ := rfl
  bind_pure_comp _ _ := rfl
  bind_map _ _ := rfl
  pure_bind _ _ := rfl
  bind_assoc x f g := by
    funext s
    dsimp only [EST.bind, bind]
    cases x s <;> rfl

instance : LawfulMonadAttach (EST ε σ) where
  map_attach {_ x} := funext fun s =>
    match h : x s with
    | .ok b c => by
      simp [Functor.map, EST.bind, MonadAttach.attach, EST.pure]
      split <;> grind
    | .error _ _ => by
      simp [Functor.map, EST.bind, MonadAttach.attach, EST.pure]
      split <;> grind
  canReturn_map_imp := by
    intro _ _ x _ ⟨s, _, hxs⟩
    cases h : x s with
      simp only [Functor.map, EST.bind, h] at hxs
    | ok val _ =>
      cases hxs
      exact val.property
    | error _ _ => contradiction

end EST
