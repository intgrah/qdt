module

public import Init.Control.Lawful.MonadAttach.Lemmas
public import Init.System.ST
public import Init.System.IO

@[expose] public section

namespace Incremental

variable {ε σ : Type}

/-!
Just assume `ST` and `EST` are well behaved...

See LawfulEst_.lean
-/

axiom ST.instLawfulMonad : LawfulMonad (ST σ)
attribute [instance] ST.instLawfulMonad
axiom ST.lawfulMonadAttach : LawfulMonadAttach (ST σ)
attribute [instance] ST.lawfulMonadAttach
axiom EST.instLawfulMonad : LawfulMonad (EST ε σ)
attribute [instance] EST.instLawfulMonad
axiom EST.lawfulMonadAttach : LawfulMonadAttach (EST ε σ)
attribute [instance] EST.lawfulMonadAttach

instance : LawfulMonad BaseIO := inferInstanceAs (LawfulMonad (ST IO.RealWorld))
instance : LawfulMonadAttach BaseIO := inferInstanceAs (LawfulMonadAttach (ST IO.RealWorld))
instance : LawfulMonad (EIO ε) := inferInstanceAs (LawfulMonad (EST ε IO.RealWorld))
instance : LawfulMonadAttach (EIO ε) := inferInstanceAs (LawfulMonadAttach (EST ε IO.RealWorld))

end Incremental
